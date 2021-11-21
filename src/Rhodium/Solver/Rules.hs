-- | A module describing the different OutsideIn(X) rules and their result
module Rhodium.Solver.Rules where

-- | The OutsideIn(X) rules
data Rule
    = Canon
    | Interact
    | Simplify
    | TopLevelReact
    | Substitution
    deriving (Eq, Show)


-- | The result of a rule application
data RuleResult a = 
    NotApplicable -- ^ The rule could not be applied
    | Applied a -- ^ The rule was successfully applied
    | Error ErrorLabel -- ^ The rule caused an error
    deriving Show

-- | Determines whether two RuleResults are of the same type, but does not compare the actual result when a rule is applied or an error is thrown
instance Eq (RuleResult a) where
    NotApplicable == NotApplicable = True
    Applied _ == Applied _ = True
    Error _ == Error _ = True
    _ == _ = False

-- | The label attached to an error
data ErrorLabel 
    = ErrorLabel String -- ^ The error label
    | NoErrorLabel -- ^ No error label could be given
    deriving (Eq)

-- | The Show instance for ErrorLabel
instance Show ErrorLabel where
    show (ErrorLabel e) = e
    show (NoErrorLabel) = "No Error Label"

-- | Check whether the result was an error
isErrorResult :: RuleResult a -> Bool
isErrorResult (Error _) = True
isErrorResult _ = False

-- | Get the error label from a RuleResult
getErrorLabel :: RuleResult a -> ErrorLabel
getErrorLabel (Error el) = el
getErrorLabel _ = error "Trying to get error from non-error result"

-- | Check if a rule was applied and return the result as a Maybe
isApplied :: RuleResult a -> Maybe a
isApplied (Applied a) = Just a
isApplied _ = Nothing

-- | Label for residual constraints
labelResidual :: ErrorLabel
labelResidual = ErrorLabel "Residual constraint"

-- | Label for incorrect constructors
labelIncorrectConstructors :: ErrorLabel
labelIncorrectConstructors = ErrorLabel "Incorrect constructors"

-- | Label for infinite types
labelInfiniteType :: ErrorLabel
labelInfiniteType = ErrorLabel "Infinite type"