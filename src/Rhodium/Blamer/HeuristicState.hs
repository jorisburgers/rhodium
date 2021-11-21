-- | A module containting a heuristic state in which information about heuristic solving might be stored
module Rhodium.Blamer.HeuristicState where

import Rhodium.Blamer.Heuristics

-- | A data type representing the heuristic state
data HeuristicState m axiom touchable types constraint ci = HeuristicState{
    heuristics :: [Heuristic m axiom touchable types constraint ci]
} deriving Show

-- | An empty heuristic state
emptyHeuristicState = HeuristicState []