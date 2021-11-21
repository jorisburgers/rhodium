{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MonoLocalBinds #-}
-- | 
module Rhodium.TypeGraphs.GraphReset where

import qualified Data.Map as M
import Data.List

import Rhodium.TypeGraphs.Graph
import Rhodium.TypeGraphs.GraphUtils
import Rhodium.TypeGraphs.GraphProperties
import Rhodium.TypeGraphs.Touchables

import Rhodium.Solver.Simplifier

import Debug.Trace

-- | Reset a list of edges
resetEdges :: (Show touchable, Show types, Show constraint) => [TGEdge constraint] -> TGGraph touchable types constraint ci -> TGGraph touchable types constraint ci
resetEdges es g = let 
    influences = nub (concatMap (getInfluences g . edgeId) es) \\ map edgeId es
    in foldr resetEdge (deleteEdges influences g) es

-- | Reset a single edge
resetEdge :: Show constraint => TGEdge constraint -> TGGraph touchable types constraint ci -> TGGraph touchable types constraint ci
resetEdge e g = g{
                edges = M.adjust (\e -> e{
                    edgeCategory = (edgeCategory e){
                        isResolved = [([0], UnResolved)],
                        influences = [],
                        rulesTried = []
                        }
                    }) (edgeId e) (edges g),
                unresolvedConstraints = e{
                        edgeCategory = (edgeCategory e){
                            isResolved = [([0], UnResolved)],
                            influences = [],
                            rulesTried = []
                        }
                    } : unresolvedConstraints g
            }

-- | Delete a list of edges
deleteEdges :: [EdgeId] -> TGGraph touchable types constraint ci -> TGGraph touchable types constraint ci
deleteEdges es g = foldr deleteEdge g es

-- | Delete a single edge
deleteEdge :: EdgeId -> TGGraph touchable types constraint ci -> TGGraph touchable types constraint ci
deleteEdge e g = g{
        edges = M.delete e (edges g),
        unresolvedConstraints = filter (\e' -> edgeId e' /= e) (unresolvedConstraints g)
    }

-- | Reset the entire graph
resetAll :: TGGraph touchable types constraint ci -> TGGraph touchable types constraint ci
resetAll g = let g' = g{
                edges = M.map (\e -> if isConstraintEdge e then e{
                    edgeCategory = (edgeCategory e){
                        isResolved = [([0], UnResolved)],
                        influences = [],
                        rulesTried = []
                        }
                    } else e) (M.filter original $ edges g)
                
                }
            in g'{
                unresolvedConstraints = filter original $ M.elems $ edges g' 
            }

-- | Remove an edge and reseet the entire graph
removeEdge :: (HasTypeGraph m axiom touchable types constraint ci) => EdgeId ->TGGraph touchable types constraint ci -> m (TGGraph touchable types constraint ci)
removeEdge eid g =  do
    let g' = resetAll (deleteEdge eid g)
    simplifyGraph False $ markEdgesUnresolved [0] g'

-- | Remove an edge and reseet the entire graph
removeEdges :: (HasTypeGraph m axiom touchable types constraint ci) => [EdgeId] ->TGGraph touchable types constraint ci -> m (TGGraph touchable types constraint ci)
removeEdges eids g =  do
    let g' = resetAll (deleteEdges eids g)
    simplifyGraph False $ markEdgesUnresolved [0] g'


-- | Remove all the unresolved edges
removedUnresolvedTried :: TGGraph touchable types constraint ci -> TGGraph touchable types constraint ci
removedUnresolvedTried g = let 
        ids = map edgeId (unresolvedConstraints g)
        reset k e   | k `elem` ids = e{
                            edgeCategory = (edgeCategory e){
                                rulesTried = []
                            }
                        }
                    | otherwise = e
    in g{
        edges = M.mapWithKey reset (edges g),
        unresolvedConstraints = map (\e -> reset (edgeId e) e) (unresolvedConstraints g)

    }