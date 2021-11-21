{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MonoLocalBinds #-}
-- | A module describing the heuristics that work on residual constraints
module Rhodium.Blamer.ResidualHeuristics where

import Rhodium.TypeGraphs.Graph
import Rhodium.TypeGraphs.GraphUtils
import Rhodium.TypeGraphs.GraphProperties
import Rhodium.TypeGraphs.GraphReset

import Rhodium.Blamer.Path
import Rhodium.Blamer.ErrorUtils

import Rhodium.Solver.Rules
import Rhodium.Solver.Simplifier

import Control.Monad

import Data.Maybe
import Data.List

import Debug.Trace

-- | A list of heuristics
type ResidualHeuristics m axiom touchable types constraint ci = Path m axiom touchable types constraint ci -> [ResidualHeuristic m axiom touchable types constraint ci]

-- | A residual heuristic data type that is either a voting heuristic of a filter heuristics, including a graph modifier
data ResidualHeuristic m axiom touchable types constraint ci
    = FilterResidual String 
            (HasTypeGraph m axiom touchable types constraint ci => [(constraint, EdgeId, ci, GraphModifier m axiom touchable types constraint ci)] -> m [(constraint, EdgeId, ci, GraphModifier m axiom touchable types constraint ci)])
    | VotingResidual [VotingResidualHeuristic m axiom touchable types constraint ci]

-- | A residual voting heuristic that can either be used on a single part of the path or on the entire path at once, including a graph modifier
data VotingResidualHeuristic m axiom touchable types constraint ci
    = SingleVotingResidual String 
        (HasTypeGraph m axiom touchable types constraint ci => (constraint, EdgeId, ci, GraphModifier m axiom touchable types constraint ci) -> m (Maybe (Int, String, constraint, EdgeId, ci, GraphModifier m axiom touchable types constraint ci)))
    | MultiVotingResidual String 
        (HasTypeGraph m axiom touchable types constraint ci => [(constraint, EdgeId, ci, GraphModifier m axiom touchable types constraint ci)] -> m (Maybe (Int, String, [constraint], [EdgeId], ci, GraphModifier m axiom touchable types constraint ci)))

-- | Returns the name of the voting heuristic
getVotingHeuristicName :: VotingResidualHeuristic m axiom touchable types constraint ci -> String
getVotingHeuristicName (SingleVotingResidual s _) = s
getVotingHeuristicName (MultiVotingResidual s _) = s

-- | Show instance for the residual heuristic
instance Show (ResidualHeuristic m axiom touchable types constraint  ci) where
    show (FilterResidual s _) = "Filter Heuristic: " ++ s
    show (VotingResidual vhs) = "Voting Heuristic: " ++ intercalate ", " (map show vhs)

-- | Show instance for the voting heuristic
instance Show (VotingResidualHeuristic m axiom touchable types constraint ci) where
    show (SingleVotingResidual s _) = "Single vote heuristic: " ++ s
    show (MultiVotingResidual s _) = "Multi vote heuristic: " ++ s
