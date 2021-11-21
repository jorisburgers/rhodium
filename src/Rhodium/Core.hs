{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
-- | Core module of the Rhodium solver that used OutsideIn(X)
module Rhodium.Core(
    SolveOptions(..),
    emptySolveOptions,
    SolveResult,
    solve,
    runTG,
    unifyTypes,
    unifyTypes'
) where 

import Rhodium.Blamer.ErrorUtils
import Rhodium.Blamer.Blamer
import Rhodium.TypeGraphs.Touchables
import Rhodium.TypeGraphs.GraphProperties
import Rhodium.TypeGraphs.TGState (runTG)
import Rhodium.TypeGraphs.Graph
import Rhodium.TypeGraphs.GraphUtils
import Rhodium.Solver.SolveResult (SolveResult (errors, substitution), graphToSolveResult)
import Rhodium.Solver.SolveOptions
import Rhodium.Solver.Simplifier

import Control.Monad.IO.Class (MonadIO )

-- | Given a list of axioms, given constraints, wanted constraints and a number of touchables, solve solves the constraints using OutsideIn(X)
solve :: (HasTypeGraph m axiom touchable types constraint ci, MonadIO m) => SolveOptions m axiom touchable types constraint ci -> [axiom] -> [constraint] -> [constraint] -> [touchable] -> m (SolveResult touchable types constraint ci)
solve options axioms given wanted touchables = do
    initializeAxioms axioms
    g <- constructGraph given wanted touchables
    setGraph g
    simpG <- simplifyGraph (includeTouchables options) g
    if typeErrorDiagnosis options && hasErrors simpG then
        blameError (typeHeuristics options) touchables simpG
    else
        return (graphToSolveResult (includeTouchables options) touchables simpG)
  
constructGraph :: (HasTypeGraph m axiom touchable types constraint ci) => [constraint] -> [constraint] -> [touchable] -> m (TGGraph touchable types constraint ci)
constructGraph given wanted touchables = do
        groupIndex <- uniqueGroup
        wanted' <- mapM (convertConstraint [] True False [groupIndex] 1) wanted
        let g = mergeGraphs emptyTGGraph wanted'
        given' <- mapM (convertConstraint [] True True [groupIndex] 0) given
        let g' = mergeGraphs g given'
        let gTouchables =  markTouchables (map (\v -> (v, 0)) touchables) g'
        setGivenTouchables (concatMap getFreeVariables given) 
        return (markEdgesUnresolved [0] gTouchables)

-- | Solves the given constraints and either returns a substitution or Nothing. Gives manual control over the solve options
unifyTypes' :: (HasTypeGraph m axiom touchable types constraint ci, MonadIO m) => SolveOptions m axiom touchable types constraint ci -> [axiom] -> [constraint] -> [constraint] -> [touchable] -> m (Maybe [(touchable, types)])
unifyTypes' opts axioms given wanted touchables =
    if null given && null wanted && null touchables then
        return (Just []) 
    else do
        let options = disableErrorDiagnosis opts
        res <- solve options axioms given wanted touchables 
        return (
            if null (errors res) then 
                Just (substitution res)
            else
                Nothing
            )
-- | Solves the given constraints and either returns a substitution or Nothing. 
unifyTypes :: (HasTypeGraph m axiom touchable types constraint ci, MonadIO m) => [axiom] -> [constraint] -> [constraint] -> [touchable] -> m (Maybe [(touchable, types)])
unifyTypes = unifyTypes' emptySolveOptions
