-- | The options the solver uses
module Rhodium.Solver.SolveOptions where

import Rhodium.Blamer.Heuristics
import Rhodium.Blamer.ResidualHeuristics
import Rhodium.Blamer.Path

-- | The solver options
data SolveOptions m axiom touchable types constraint ci = SolveOptions{
    typeHeuristics :: Path m axiom touchable types constraint ci -> [Heuristic m axiom touchable types constraint ci],
    residualHeuristics :: ResidualHeuristics m axiom touchable types constraint ci,
    typeErrorDiagnosis :: Bool, 
    includeTouchables :: Bool
    }

-- | No Solver options
emptySolveOptions = SolveOptions {
        typeHeuristics = const [],
        residualHeuristics = const [],
        typeErrorDiagnosis = True,
        includeTouchables = False
    }

-- | Disables the process of type error diagnosis. Can be used when the only information of interest is success or failure, not which exact error has occured.
disableErrorDiagnosis options = options{
    typeErrorDiagnosis = False
    }

-- | Ignore any problems with touchability, might cause incorrect programs to be accepted, but can be used to inspect the types inside existentital constraints    
ignoreTouchables options = options{
    includeTouchables = True
}
