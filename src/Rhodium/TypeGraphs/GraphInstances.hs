{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | A number of default instances for TGState
module Rhodium.TypeGraphs.GraphInstances where

import Control.Monad.Trans.State (get, put)

import Data.List

import Rhodium.TypeGraphs.GraphProperties
import Rhodium.TypeGraphs.TGState
import Rhodium.TypeGraphs.Graph


-- | An instance for storing the axioms in the TGState
instance Monad m => HasAxioms (TGStateM m axiom touchable types constraint ci) axiom where
    -- initializeAxioms :: [axiom] -> m ()
    initializeAxioms axioms' = do
        state <- get
        put (state{axioms = axioms'})  
    -- getAxioms :: m [axiom]
    getAxioms = do
        state <- get
        return (axioms state)

-- | An instance for getting a unique vertex id based on the TGState
instance Monad m => UniqueVertex (TGStateM m axiom touchable types constraint ci) where
    uniqueVertex = do
        state <- get
        let curId = vertexIndex state
        put (state{vertexIndex = curId + 1})
        return curId
    setUniqueVertex v = do
        state <- get
        put (state{
            vertexIndex = v
        })
-- | An instance for getting a unique edge id based on the TGState
instance Monad m => UniqueEdge (TGStateM m axiom touchable types constraint ci) where
    uniqueEdge = do
        state <- get
        let curId = edgeIndex state
        put (state{edgeIndex = curId + 1})
        return curId
    setUniqueEdge v = do
            state <- get
            put (state{
                edgeIndex = v
            })


-- | An instance for getting a unique group from a TGState
instance Monad m => UniqueGroup (TGStateM m axiom touchable types constraint ci) where
    uniqueGroup = do
        state <- get
        let curId = groupIndex state
        put (state{groupIndex = curId + 1})
        return curId

-- | An instance for detecting which variables are touchable in a graph
instance (Show axiom, Ord touchable, Monad m, Show touchable, Show types, Show constraint, Eq touchable, Eq types, Eq constraint, HasGraph (TGStateM m axiom touchable types constraint ci) touchable types constraint ci) => IsTouchable (TGStateM m axiom touchable types constraint ci) touchable where
    isVertexTouchable t = do 
        g <- getGraph
        return (maybe Nothing isTouchable (find (\v -> getVariable v == Just (Variable t)) $ vertices g))
    greaterTouchable t1 t2 = do 
        state <- get 
        tt1 <- isVertexTouchable t1
        tt2 <- isVertexTouchable t2  
        let gT1 = t1 `elem` givenVariables state || maybe False even tt1 
        let gT2 = t2 `elem` givenVariables state || maybe False even tt2
        case (gT1, gT2) of
            (True, False) -> return True
            (False, True) -> return False 
            _ -> case (tt1, tt2) of
                (Just p1, Just p2) -> 
                    return (
                        if p1 == p2 then
                            t1 > t2
                        else
                            p1 < p2
                        {-if (p1 < currentPrior && p2 < currentPrior) || p1 == p2 then
                            t1 > t2
                        else if p2 >= currentPrior && p1 < currentPrior then
                            True
                        else if p1 >= currentPrior && p2 < currentPrior then
                            False
                        else (p1 >= currentPrior) && ((p2 < currentPrior) || (t1 > t2))-}
                        )
                (Just _, Nothing) -> return False
                (Nothing, Just _) -> return True
                _ -> return (t1 > t2)
    setGivenTouchables touchables = do
        s <- get
        put (s{
            givenVariables = nub (givenVariables s ++ touchables)
        })
    getGivenTouchables = givenVariables <$> get


-- | An instance for the default graph in TGState
instance (ConvertConstructor types, Show constraint, Show types, Show touchable, Ord types, Eq constraint, Eq touchable, Monad m, CanCompareTouchable touchable types) => HasGraph (TGStateM m axiom touchable types constraint ci) touchable types constraint ci where
    --getGraph :: m (TGGraph touchable constraint types)
    getGraph = do
        state <- get
        return (graph state)
    setGraph g = do
        state <- get
        put(state{graph = g})
    setPriority p = do
        state <- get
        put(state{currentPriority = p})
    getPriority = do
        state <- get
        return (currentPriority state)
    ruleIsApplied r c s = do
        state <- get
        put (state{isGraphRuleApplied = True, rulesApplied = (r, c, s) : rulesApplied state})
    isRuleApplied = isGraphRuleApplied <$> get
    getAppliedRules = rulesApplied <$> get
    resetRuleApplied = do
        state <- get
        put (state{isGraphRuleApplied = False, rulesApplied = []})

-- | Allows the writing of logging information that can be used for debugging information
instance Monad m => HasLogInfo (TGStateM m axiom touchable types constraint ci) where
    logMsg msg = do
        state <- get 
        put (state{
                logs = msg : logs state
            })
    getLogs = ("Log messages: \n"++) . unlines . reverse . logs <$> get 

-- | Store the original constraints for later inspection
instance Monad m => HasOriginalConstraints (TGStateM m axiom touchable types constraint ci) constraint touchable where
    setOriginalInput input = do
        state <- get
        put state{
            originalInput = input
        }
    getOriginalInput = originalInput <$> get