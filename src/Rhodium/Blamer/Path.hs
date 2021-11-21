{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
-- | A module describing error paths
module Rhodium.Blamer.Path where

import Data.List
import Data.Maybe
import qualified Data.Map as M

import Rhodium.TypeGraphs.Graph
import Rhodium.TypeGraphs.GraphReset
import Rhodium.TypeGraphs.GraphProperties
import Rhodium.TypeGraphs.GraphUtils
import Rhodium.TypeGraphs.Touchables
import Rhodium.Solver.Rules

import Rhodium.Blamer.ErrorUtils

import Debug.Trace

-- | A modifier that can modify a graph based on a residual error
type GraphModifier m axiom touchable types constraint ci = (EdgeId, constraint, ci) -> TGGraph touchable types constraint ci -> m (TGGraph touchable types constraint ci, ci)

-- | An error path consisting of constraints
data Path m axiom touchable types constraint ci = Path (EdgeId, constraint, ErrorLabel) [(constraint, EdgeId, ci, GraphModifier m axiom touchable types constraint ci)]

-- | Show instance for the path
instance (Show constraint) => Show (Path m axiom touchable types constraint ci) where
    show p@(Path (eid, constraint, el) ids) = "Path(" ++ show eid ++ ", " ++ show constraint ++ ", " ++ show el ++ ") " ++ show (idsFromPath p)

instance (Eq constraint) => Eq (Path m axiom touchable types constraint ci) where
    (Path t1 ids1) == (Path t2 ids2) = t1 == t2 && let f = map (\(c, eid, _, _) -> (c, eid)) in f ids1 == f ids2


-- | Extends a list of path to include all relevant constraints
extendErrorEdges ::  (Show constraint, HasConstraintInfo constraint ci, Eq constraint) => GraphModifier m axiom touchable types constraint ci -> ([TGEdge constraint] -> [(TGEdge constraint, ErrorLabel)]) -> TGGraph touchable types constraint ci -> [Path m axiom touchable types constraint ci]
extendErrorEdges gm f g = let 
    errorEdges = f (M.elems $ edges g)
    se = map (\(edge, label) -> ((edgeId edge, getConstraintFromEdge edge, label), getPath g edge)) errorEdges
    --cg = sortOn snd $ map (\s -> (head s, length s)) se
    res = map (\(l, es) -> Path l $ mapMaybe (\e -> let ci = getConstraintInfo (getConstraintFromEdge e) in 
            if isJust ci then 
                Just (getConstraintFromEdge e, edgeId e, fromJust ci, gm)
            else 
                Nothing -- error $ "Constraint is missing constraint info: " ++ show (getConstraintFromEdge e)
            ) es) se
    in if any isPathEmpty res then error $ show ("Path empty", res) else res

-- | Return all the type error edges
getProblemEdges :: HasTypeGraph m axiom touchable types constraint ci => TGGraph touchable types constraint ci -> [Path m axiom touchable types constraint ci]
getProblemEdges g =  mergePaths (extendErrorEdges defaultRemoveModifier getErrorEdges g ++ extendErrorEdges defaultRemoveModifier (getResidualEdges g) g)

mergePaths :: (Ord constraint, Show constraint, Eq constraint) => [Path m axiom touchable types constraint ci] -> [Path m axiom touchable types constraint ci]
mergePaths = nubBy same . map merge . groupBy same . sortOn constraintFromPath
        where
            same :: (Show constraint, Eq constraint) => Path m axiom touchable types constraint ci -> Path m axiom touchable types constraint ci -> Bool
            same (Path (_, c1, l1) p1) (Path (_, c2, l2) p2) = c1 == c2 && l1 == l2 -- && (map idFromTuple p1 `isInfixOf` map idFromTuple p2 || map idFromTuple p2 `isInfixOf` map idFromTuple p1)
            idFromTuple (_, eid, _, _) = eid
            merge = foldr1 mergeP
            mergeP (Path (eid1, c1, l1) ids1) (Path _ ids2) = Path (eid1, c1, l1) (unionBy (\(_, eid1, _, _) (_, eid2, _, _) -> eid1 == eid2) ids1 ids2)

-- | Get a list of ids from a path
idsFromPath :: Path m axiom touchable types constraint ci -> [EdgeId]
idsFromPath (Path _ ps) = map (\(_, ei, _, _) -> ei) ps

-- | Get the original error constraint from the path
constraintFromPath :: Path m axiom touchable types constraint ci -> constraint
constraintFromPath (Path (_, constraint, _) _) = constraint

labelFromPath :: Path m axiom touchable types constraint ci -> ErrorLabel
labelFromPath (Path (_, _, l) _) = l

-- | Get the original error edge from the path
edgeIdFromPath :: Path m axiom touchable types constraint ci -> EdgeId
edgeIdFromPath (Path (eid, _, _) _) = eid

-- | Remove a number of edges from the path
excludeEdges :: [EdgeId] -> Path m axiom touchable types constraint ci -> Path m axiom touchable types constraint ci
excludeEdges excludes (Path l ps) = Path l (filter (\(_, eid, _, _) -> eid `notElem` excludes) ps )

-- | Returns a participation map from a list of paths
participationMap :: Show constraint => [Path m axiom touchable types constraint ci] -> (Integer, M.Map EdgeId Integer)
participationMap paths = let 
        maps =  map participationMap' paths
        combined = foldr (M.unionWith (+)) M.empty maps
    in if null combined && not (null paths) then error $ show ("Combined empty null", paths) else (maximum combined, combined)
        where
            participationMap' p = M.fromList $ map (\e -> (e, 1)) $ idsFromPath p
-- | Creates an empty path
emptyPath :: HasTypeGraph m axiom touchable types constraint ci => Path m axiom touchable types constraint ci
emptyPath = Path (undefined, undefined, NoErrorLabel) []

defaultRemoveModifier :: HasTypeGraph m axiom touchable types constraint ci => GraphModifier m axiom touchable types constraint ci
defaultRemoveModifier (eid, constraint, ci) g = removeEdge eid g >>= \g' -> return (g', ci)


-- | Creates a default graph modifier, either adding a new given constraint or making an untouchable variable touchable
defaultResidualGraphModifier :: HasTypeGraph m axiom touchable types constraint ci => GraphModifier m axiom touchable types constraint ci
defaultResidualGraphModifier (eid, constraint, ci) graph = 
    do 
    let edge = getEdgeFromId graph eid
    let g = resetAll graph
    if isEdgeGiven edge then do
        g' <- removeEdge eid g 
        return (markTouchables (map (\fv -> (fv, getPriorityFromEdge edge)) (getFreeVariables (getConstraintFromEdge edge))) g', ci)
    else do
        sg <- convertConstraint [] True True (getGroupFromEdge edge) (getPriorityFromEdge edge) (getConstraintFromEdge edge)
        return (mergeGraph g sg, ci)
-- | Check if the path is empty, which should never occur
isPathEmpty :: Path m axiom touchable types constraint ci -> Bool
isPathEmpty (Path _ xs) = null xs

isResidualPath (Path (_, _, l) _) = l == labelResidual

constraintsFromPath (Path _ cs) = map (\(c, _, _, _) -> c) cs

sortPaths :: Show constraint => [Path m axiom touchable types constraint ci] -> [Path m axiom touchable types constraint ci]
sortPaths = sortBy sp
    where
        sp p1 p2    | labelFromPath p1 /= labelResidual && labelFromPath p2 == labelResidual = LT
                    | labelFromPath p1 == labelResidual && labelFromPath p2 /= labelResidual = GT
                    | otherwise = let
                        ip1 = idsFromPath p1
                        ip2 = idsFromPath p2
                        in case (ip1 `isInfixOf` ip2, ip2 `isInfixOf` ip1) of
                            (False, True) -> LT
                            (True, False) -> GT
                            _ -> compare (length ip1) (length ip2)