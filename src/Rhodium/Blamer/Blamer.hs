{-# LANGUAGE MonoLocalBinds #-}
-- | Interface for blaming errors on certain constraints using heuristics
module Rhodium.Blamer.Blamer(
    blameError
) where

import Rhodium.Blamer.ErrorUtils
import Rhodium.Blamer.Path
import Rhodium.Blamer.Heuristics
import Rhodium.Blamer.HeuristicProperties

import Rhodium.Solver.SolveResult
import Rhodium.Solver.Simplifier
import Rhodium.TypeGraphs.Graph
import Rhodium.TypeGraphs.GraphUtils
import Rhodium.TypeGraphs.GraphProperties as GP

import Data.List
import Control.Monad.IO.Class (MonadIO, liftIO  )
import qualified Data.Map as M

import Control.Arrow


-- | Try to improve the found errors and residual constraints using the provided heuristics
blameError :: (HasTypeGraph m axiom touchable types constraint ci, MonadIO m ) => Heuristics m axiom touchable types constraint ci -> [touchable] -> TGGraph touchable types constraint ci -> m (SolveResult touchable types constraint ci)
blameError typeHeuristics ts g = do
    -- all paths
    g'' <- blamePaths [] typeHeuristics g
    simpG <- simplifyGraph False g''
    simpG' <- modifyResolvedErrors createTypeError simpG
    logs <- getLogs
    liftIO (putStrLn logs)
    return (graphToSolveResult False ts simpG')

blamePaths :: (HasTypeGraph m axiom touchable types constraint ci ) => [EdgeId] -> Heuristics m axiom touchable types constraint ci -> TGGraph touchable types constraint ci -> m (TGGraph touchable types constraint ci)
blamePaths notAllowedInPaths typeHeuristics g = do
    setGraph g
    let ps = sortPaths $ map (excludeEdges notAllowedInPaths) $ getProblemEdges g
    if any isPathEmpty ps then
        error $ show ("Any path empty", notAllowedInPaths)
    else if null ps then
        return g
    else do
        logMsg ("Number of paths: " ++ show (length ps))
        logMsg ("All Paths: " ++ show (map (\p@(Path l _) -> (idsFromPath p, show l)) ps))
        let errorIds = nub (concatMap idsFromPath ps)
        logMsg (unlines $ map (\e -> "    " ++ show ((\err -> (err, getConstraintFromEdge $ getEdgeFromId g err)) e)) errorIds)
        (g', errorInfo) <- applyHeuristics typeHeuristics (head ps) g
        let nErrors = map (first getConstraintFromEdge) $ getErrorEdges $ M.elems $ edges g'
        let oErrors = map (first getConstraintFromEdge) $ getErrorEdges $ M.elems $ edges g
        logMsg $ "Before: " ++ show oErrors
        logMsg $ "After: " ++ show nErrors
        logMsg "Error blamed"
        logMsg ("  Path: " ++ show (idsFromPath $ head ps))
        logMsg ("  Solution: " ++ show errorInfo)
        blamePaths notAllowedInPaths typeHeuristics g'

