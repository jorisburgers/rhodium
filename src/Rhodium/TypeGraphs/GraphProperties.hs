{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- | A module containing possible properties of a type graph
module Rhodium.TypeGraphs.GraphProperties where

import Rhodium.Solver.Rules
import Rhodium.TypeGraphs.Touchables
import Rhodium.TypeGraphs.Graph

import Rhodium.Blamer.HeuristicProperties

import qualified Data.Map.Strict as M

-- | The constraint has a canon rule
class CanCanon m touchable types constraint | m -> touchable types constraint where
    -- | The canon rule
    canon   :: Bool -- ^ Whether the constraint was given 
            -> constraint -- ^ The constraint
            -> m (RuleResult ([touchable], [(touchable, types)], [constraint])) -- ^ The result, with a list of new touchables, a substitution and a list of new constraints

-- | The constraint has a interact rule
class Monad m => CanInteract m touchable types constraint ci | m -> touchable types constraint ci where
    -- | The interact rule
    interact    :: Bool -- ^ Whether the constraint was given
                -> constraint -- ^ The first constraint
                -> constraint -- ^ The second constraint
                -> m (RuleResult [constraint]) -- The result, with a list of new constraints
    -- | Returns a list with all other constraint that need to be tried with the given constrain. 
    getInteractionCandidates    :: [EdgeId] -- ^The edge ids of the vertices that can be ignored
                                -> TGEdge constraint -- ^ The constraint that will be tried with the interact rule
                                -> TGGraph touchable types constraint ci -- ^ The graph in which the edge is located
                                -> m [TGEdge constraint] -- ^ A list of edges that will be combined by the current given edge, it is always safe to return all the edges in the graph
    getInteractionCandidates d _ g = return (filter (\e -> edgeId e `notElem` d) $ M.elems $ edges g)

-- | Two constraints can be simplified
class Monad m => CanSimplify m touchable types constraint ci | m -> touchable types constraint ci where
    -- | Simplify a given and a wanted constraint
    simplify    :: constraint -- ^ The given constraint
                -> constraint -- ^ The wanted constraint
                -> m (RuleResult [constraint])
    -- | Return a list of possible edges to explore
    getSimplificationCandidates  :: [EdgeId] -- ^The edge ids of the vertices that can be ignored
                                -> TGEdge constraint 
                                -> TGGraph touchable types constraint ci
                                -> m [TGEdge constraint]
    getSimplificationCandidates d _ g = return (filter (\e -> edgeId e `notElem` d) $ M.elems $ edges g) 

-- | A constraint can be used in comparison with a top level axiom
class (HasAxioms m axiom, Monad m) => CanTopLevelReact m axiom touchable types constraint | m -> axiom touchable types constraint where
    -- | Using whether the constraint is given or wanted, return a list of possible new touchables and a list of new constraints
    topLevelReact   :: Bool 
                    -> constraint 
                    -> m (RuleResult ([touchable], [constraint]))

-- | The type graph has a list of axioms
class HasAxioms m axiom | m -> axiom where 
    -- | Initialize the list of axioms
    initializeAxioms :: [axiom] -> m ()
    -- | Returns the list of axioms
    getAxioms :: m [axiom]

-- | The monad has a type graph on which it currently works
class HasGraph m touchable types constraint ci | m -> touchable types constraint ci where
    -- | Return the current graph
    getGraph :: m (TGGraph touchable types constraint ci)
    -- | Indicates that a rule is applied
    ruleIsApplied :: Rule -> [constraint] -> String -> m ()
    -- | Ask if a rule is applied, if no rule is applied, the simplifier can stop
    isRuleApplied :: m Bool
    -- | Reset whether the rule is applied
    resetRuleApplied :: m ()
    -- | Get the rules that are applied
    getAppliedRules :: m [(Rule, [constraint], String)]
    -- | Set the current graph
    setGraph :: TGGraph touchable types constraint ci -> m ()
    -- | Sets the priority
    setPriority :: Priority -> m ()
    -- | Returns the current priority
    getPriority :: m Priority

-- | Gives a unique vertex number
class Monad m => UniqueVertex m where
    -- | Returns the unique vertex number
    uniqueVertex :: m VertexId
    setUniqueVertex :: VertexId -> m ()

-- | Gives a unique edge number
class Monad m => UniqueEdge m where
    -- | Returns the unique edge number
    uniqueEdge :: m EdgeId
    setUniqueEdge :: EdgeId -> m ()

-- | Gives a unique group number
class Monad m => UniqueGroup m where
    -- | Returns the unique group number
    uniqueGroup :: m GroupId

-- | The type graph can convert a type into a type graph
class UniqueVertex m => CanConvertType m touchable types constraint ci | m -> touchable types constraint ci where
    -- | The type can be converted into a new graph and a vertex id, which should be present in the graph and indicates which node represents the entire graph
    convertType :: Bool -> Groups -> Priority -> types -> m (TGGraph touchable types constraint ci, VertexId)


-- | The type graph can convert a constraint into a type graph
class (CanConvertType m touchable types constraint ci, UniqueVertex m) => CanConvertConstraint m touchable types constraint ci | m -> touchable types constraint ci where
    -- | The constraint can be converted into a type graph
    convertConstraint   :: [EdgeId] -- ^ A list of edges on which the new constraint is based
                        -> Bool -- ^ Whether the constraint is original
                        -> Bool -- ^ Whether the constraint is given (or wanted)
                        -> Groups
                        -> Priority
                        -> constraint -- ^The constraint
                        -> m (TGGraph touchable types constraint ci) -- ^ The resulting graph that represent the constraint

-- | Converts the constraint into a symbol, used for showing the symbol in a visual representation
class ConstraintSymbol constraint where
    -- | Converts the constraint into a symbol for that constraint
    showConstraintSymbol :: constraint -> String

-- | To handle equaltiy constraints
class IsEquality types constraint touchable | constraint -> types touchable where
    -- | Determines whether a constraint is an equiltiy constraint (~)
    isEquality :: constraint -> Bool
    -- | Split the equaltiy constraint into a left and a right part
    splitEquality :: constraint -> (types, types)
    -- | Excludes constraints from substitution, for example for containting type families
    allowInSubstitution :: constraint -> Bool

   
-- | Detecting whether a variable is touchable in the current scope
class IsTouchable m touchable where
    -- | Given a variable, deciding whether this is touchable
    isVertexTouchable :: touchable -> m (Maybe Int)
    -- | Compare two touchable
    greaterTouchable :: touchable -> touchable -> m Bool
    -- | Set the given touchables in the current state
    setGivenTouchables :: [touchable] -> m ()
    getGivenTouchables :: m [touchable]

-- | Compapre two type
class CompareTypes m types where
    -- | Determine whether the first type is larger than the second type
    greaterType :: types -> types -> m Bool 

    mgu :: [types] -> m types

-- | Get the free variables from a source
class FreeVariables source target | source -> target where
    -- | Convert the free variables from the source
    getFreeVariables :: source -> [target]

    getFreeTopLevelVariables :: source -> [target]

-- | Get and set the constraint information
class HasConstraintInfo constraint ci | constraint -> ci where
    getConstraintInfo :: constraint -> Maybe ci
    setConstraintInfo :: ci -> constraint -> constraint

-- | Can store log message for debugging purposes
class HasLogInfo m where
    logMsg :: String -> m ()
    getLogs :: m String

-- | Store and retrieve the original input
class HasOriginalConstraints m constraint touchable | m -> constraint touchable where
    setOriginalInput :: ([constraint], [constraint], [touchable]) -> m ()
    getOriginalInput :: m ([constraint], [constraint], [touchable])


-- | All the properties combined into a single type class
class (
        FreshVariable m touchable
    ,   HasAxioms m axiom
    ,   HasGraph m touchable types constraint ci
    ,   CanCanon m touchable types constraint 
    ,   CanInteract m touchable types constraint ci
    ,   CanSimplify m touchable types constraint ci
    ,   CanTopLevelReact m axiom touchable types constraint
    ,   CanConvertType m touchable  types constraint ci
    ,   CanConvertConstraint m touchable  types constraint ci
    ,   ConvertConstructor types
    ,   CanCompareTouchable touchable types
    ,   IsEquality types constraint touchable
    ,   IsTouchable m touchable
    ,   FreeVariables constraint touchable
    ,   FreeVariables types touchable
    ,   UniqueVertex m
    ,   UniqueEdge m
    ,   UniqueGroup m
    ,   Show axiom
    ,   Show touchable 
    ,   Show constraint
    ,   Show types
    ,   Show ci
    ,   Eq touchable
    ,   Eq constraint
    ,   Ord types
    ,   Ord constraint
    ,   ConstraintSymbol constraint
    ,   HasConstraintInfo constraint ci
    ,   HasLogInfo m
    ,   TypeErrorInfo m constraint ci
    ,   HasOriginalConstraints m constraint touchable
    ) => HasTypeGraph m axiom touchable types constraint ci
    
-- | An instance, if all necessary properties are given, the type graph instance exists
instance (
        FreshVariable m touchable
    ,   HasAxioms m axiom
    ,   HasGraph m touchable types constraint ci
    ,   CanCanon m touchable types constraint 
    ,   CanInteract m touchable types constraint ci
    ,   CanSimplify m touchable types constraint ci
    ,   CanTopLevelReact m axiom touchable types constraint
    ,   CanConvertType m touchable  types constraint ci
    ,   CanConvertConstraint m touchable  types constraint ci
    ,   ConvertConstructor types
    ,   CanCompareTouchable touchable types
    ,   IsEquality types constraint touchable
    ,   IsTouchable m touchable
    ,   FreeVariables constraint touchable
    ,   FreeVariables types touchable
    ,   UniqueVertex m
    ,   UniqueEdge m
    ,   UniqueGroup m
    ,   Show axiom
    ,   Show touchable 
    ,   Show constraint
    ,   Show types
    ,   Show ci
    ,   Eq touchable
    ,   Eq constraint
    ,   Ord types
    ,   Ord constraint
    ,   ConstraintSymbol constraint 
    ,   HasConstraintInfo constraint ci
    ,   HasLogInfo m
    ,   TypeErrorInfo m constraint ci
    ,   HasOriginalConstraints m constraint touchable
    ) => HasTypeGraph m axiom touchable types constraint ci
    
         