-- | The state of the type graph solver
module Rhodium.TypeGraphs.TGState(
    runTG,
    emptyTGState,
    TGStateM,
    TGState(..)
) where



import Control.Monad.Trans.State

import Rhodium.TypeGraphs.Graph
import Rhodium.Solver.Rules

import Rhodium.Blamer.HeuristicState

-- | Represents the state of the type graph solver
type TGStateM m axiom touchable types constraint ci = StateT (TGState m axiom touchable types constraint ci) m

-- | Runs TGStateM monad
runTG :: Monad m => TGStateM m axiom touchable types constraint ci a -> m a
runTG s = evalStateT s emptyTGState 

-- | Stores all meta information about a type graph
data TGState m axiom touchable types constraint ci = TGState{
    axioms :: [axiom],
    vertexIndex :: Int,
    edgeIndex :: Int,
    groupIndex :: Int,
    graph :: TGGraph touchable types constraint ci,
    isGraphRuleApplied :: Bool,
    rulesApplied :: [(Rule, [constraint], String)],
    currentPriority :: Priority,
    givenVariables :: [touchable],
    heuristicState :: HeuristicState m axiom touchable types constraint ci,
    logs :: [String],
    originalInput :: ([constraint], [constraint], [touchable])
} deriving Show

-- | Return an empty TGState
emptyTGState :: TGState m axiom touchable types constraint ci
emptyTGState = TGState{
    axioms = [],
    graph = emptyTGGraph,
    vertexIndex = 0,
    edgeIndex = 0,
    groupIndex = 0,
    isGraphRuleApplied = False,
    currentPriority = 0,
    givenVariables = [],
    rulesApplied = [],
    heuristicState = emptyHeuristicState,
    logs = [],
    originalInput = ([], [], [])
}




