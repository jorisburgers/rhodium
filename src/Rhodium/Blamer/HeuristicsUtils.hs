module Rhodium.Blamer.HeuristicsUtils where

import Rhodium.TypeGraphs.Graph
import Rhodium.TypeGraphs.GraphUtils
import Rhodium.TypeGraphs.GraphProperties
import Rhodium.TypeGraphs.GraphReset

import qualified Data.Map as M

import Debug.Trace

doWithoutConstraint :: (HasTypeGraph m axiom touchable types constraint ci) => constraint -> m a -> m a
doWithoutConstraint constraint comp = do
    graph <- getGraph
    let eids = map edgeId $ filter (\e -> isConstraintEdge e && getConstraintFromEdge e == constraint) (M.elems $ edges graph)
    graph' <- removeEdges eids graph
    setGraph graph'
    res <- comp
    setGraph graph
    return res

doWithoutEdge :: (HasTypeGraph m axiom touchable types constraint ci) => EdgeId -> m a -> m a
doWithoutEdge edgeId comp = do
    graph <- getGraph
    graph' <- removeEdge edgeId graph
    setGraph graph'
    res <- comp
    setGraph graph
    return res

    