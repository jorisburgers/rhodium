{-# LANGUAGE MultiParamTypeClasses #-}
-- | Module for describing properties of heuristics or properties that heuristics use
module Rhodium.Blamer.HeuristicProperties where
    
import Rhodium.Solver.Rules
import Rhodium.TypeGraphs.Graph

-- | Can create the type error
class TypeErrorInfo m constraint ci where
    createTypeError :: TGEdge constraint -> ErrorLabel -> constraint -> ci -> m ci