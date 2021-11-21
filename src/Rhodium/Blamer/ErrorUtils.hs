-- | Utiltiy function for errors
module Rhodium.Blamer.ErrorUtils where

import Data.Maybe
import qualified Data.Map as M

import Control.Monad

import Rhodium.TypeGraphs.Graph
import Rhodium.TypeGraphs.GraphUtils
import Rhodium.TypeGraphs.GraphProperties

import Rhodium.Solver.Rules

import Debug.Trace

-- | Does the graph have an error in the specific group
hasErrors :: (Show touchable, Show types, Show constraint, IsEquality types constraint touchable) => TGGraph touchable types constraint ci -> Bool
hasErrors g = hasErrorEdges (M.elems (edges g)) || hasResidualEdges g (M.elems (edges g))

-- | Get all the errors in the graph with the specific group
getErrors ::  (Show touchable, Show types, Show constraint, IsEquality types constraint touchable) => TGGraph touchable types constraint ci -> [(TGEdge constraint, ErrorLabel)]
getErrors g = getErrorEdges (M.elems (edges g)) ++ getResidualConstraints g (M.elems (edges g))

-- | Does the graph have any type errors (like 'Int ~ 'Bool)
hasErrorEdges :: (Show constraint) => [TGEdge constraint] -> Bool
hasErrorEdges = not . null . getErrorEdges

-- | Does the graph have any residual errors (like Eq a)
hasResidualEdges :: (Show touchable, Show types, Show constraint, IsEquality types constraint touchable) => TGGraph touchable types constraint ci -> [TGEdge constraint] -> Bool
hasResidualEdges g = not . null . getResidualConstraints g

-- | Get all the type error edges 
getErrorEdges :: Show constraint => [TGEdge constraint] -> [(TGEdge constraint, ErrorLabel)]
getErrorEdges = map (\e -> (e, fromJust $ getIsIncorrect e)) . filter (liftM2 (&&) isConstraintEdge (isJust . getIsIncorrect))

-- | Get all the residual constraints in the specific group
getResidualConstraints :: (Show touchable, Show types, Show constraint, IsEquality types constraint touchable) => TGGraph touchable types constraint ci -> [TGEdge constraint] -> [(TGEdge constraint, ErrorLabel)]
getResidualConstraints g = map (\e -> (e, labelResidual)) . filter (\e -> isConstraintEdge e && isResidual (groups (edgeCategory e)) g e)

-- | Get all the residual constraints in all groups
getResidualEdges :: (Show touchable, Show types, IsEquality types constraint touchable, Show constraint) => TGGraph touchable types constraint ci -> [TGEdge constraint] -> [(TGEdge constraint, ErrorLabel)]
getResidualEdges gr es =  map (\e -> (e, labelResidual)) $ filter (\e -> isConstraintEdge e && isResidual (groups (edgeCategory e)) gr e) es 


-- | Add an error as resolved
addResolvedError :: (Show ci, Show constraint) => (TGEdge constraint, ci, constraint, ErrorLabel) -> TGGraph touchable types constraint ci -> TGGraph touchable types constraint ci
addResolvedError err graph = graph{
        resolvedErrors = Just (err : fromMaybe [] (resolvedErrors graph))
    }

-- | Modify the resolved errors
modifyResolvedErrors :: Monad m => (TGEdge constraint -> ErrorLabel -> constraint -> ci -> m ci) -> TGGraph touchable types constraint ci -> m (TGGraph touchable types constraint ci)
modifyResolvedErrors f graph =
        case resolvedErrors graph of
            Nothing -> return graph
            Just resErrors -> do 
                nres <- mapM (\(eid, c, cons, li) -> f eid li cons c >>= \c' -> return (eid, c', cons, li)) resErrors
                return graph{
                    resolvedErrors = Just nres
                }