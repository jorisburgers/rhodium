{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module TestGraph where

import Control.Monad.Trans.State.Lazy (State, evalState, get, put, modify)

import Data.List (nub, find)

import Rhodium.TypeGraphs.Touchables (FreshVariable (..))
import Rhodium.TypeGraphs.Graph 
  (TGGraph (vertices)
  , ConvertConstructor (..)
  , CanCompareTouchable (..)
  , TGVertexCategory (..)
  , VertexId
  , NodeValue (..)
  , emptyTGGraph
  , mergeGraphsWithEdges
  , constraintEdge
  , mergeGraph
  , typeEdge
  , singletonGraph
  , getVariable
  )
import Rhodium.TypeGraphs.GraphUtils (getVertexFromGraph)
import Rhodium.TypeGraphs.GraphProperties 
  ( HasGraph (..)
  , CanCanon (..)
  , CanInteract (..)
  , CanSimplify (..)
  , CanTopLevelReact (..)
  , HasAxioms (..)
  , CanConvertConstraint (..)
  , UniqueEdge (..)
  , UniqueVertex (..)
  , CanConvertType (..)
  , IsTouchable (..)
  , IsEquality (..)
  , FreeVariables (..)
  , UniqueGroup (..)
  , ConstraintSymbol (..)
  , HasConstraintInfo (..)
  , HasLogInfo (..)
  , HasOriginalConstraints (..)
  )
import Rhodium.Blamer.HeuristicProperties (TypeErrorInfo (..))
import Rhodium.Solver.Rules (Rule, RuleResult (..), ErrorLabel (..), labelIncorrectConstructors)


newtype Touchable = Touchable Int
  deriving (Show, Eq, Ord)

instance FreshVariable TestGraphM Touchable where
  freshVariable = do
    s <- get
    let curIndex = typeGraphEnvTouchableIndex s
    put (s {typeGraphEnvTouchableIndex = curIndex + 1 })
    pure (Touchable curIndex)

data Type 
  = TypeConstructor String
  | TypeApplication Type Type
  | TypeVariable Touchable 
  deriving (Show, Eq, Ord)

data Constraint = ConstraintUnify Type Type
  deriving (Show, Eq, Ord)

-- There is no constraint info at the moment, depending on the tests, this can be expanded
data ConstraintInfo = ConstraintInfo
  deriving (Show, Eq)

data Axiom = Axiom
  deriving (Show)

-- * Simplified instances

instance ConstraintSymbol Constraint where
  showConstraintSymbol (ConstraintUnify{}) = "~"

instance HasConstraintInfo Constraint ConstraintInfo where
    getConstraintInfo (ConstraintUnify{}) = Just ConstraintInfo
    setConstraintInfo ConstraintInfo c = c

instance HasLogInfo TestGraphM where
    -- Ingore log messages during testing
    logMsg _ = pure ()
    getLogs = pure ""

instance TypeErrorInfo TestGraphM Constraint ConstraintInfo where
  createTypeError _edge _errorLabel _constraint ci = pure ci

instance CanCanon TestGraphM Touchable Type Constraint where
  canon _isGiven constraint = do
    case constraint of 
      ConstraintUnify (TypeConstructor s) (TypeConstructor t) 
        | s == t -> pure $ Applied ([], [], [])
        | otherwise ->  pure (Error labelIncorrectConstructors)
      _ -> pure (Error NoErrorLabel)

instance CanInteract TestGraphM Touchable Type Constraint ConstraintInfo where
    interact _isGiven c1 c2
        | c1 == c2 = pure $ Applied [c1]
        | otherwise = pure (Error NoErrorLabel)

instance CanSimplify TestGraphM Touchable Type Constraint ConstraintInfo where
  simplify _c1 _c2 =pure NotApplicable

instance CanTopLevelReact TestGraphM Axiom Touchable Type Constraint where
  topLevelReact _isGiven _constraint = pure NotApplicable

instance HasAxioms TestGraphM Axiom where
    initializeAxioms _ = error "No support for axioms"
    getAxioms = error "No support for axioms"

instance CanConvertConstraint TestGraphM Touchable Type Constraint ConstraintInfo where
  convertConstraint basedOn isOriginal isGiven groups priority c@(ConstraintUnify m1 m2) = do
    (v1Node, v1) <- convertType isOriginal groups priority m1
    (v2Node, v2) <- convertType isOriginal groups priority m2
    edgeIndex <- uniqueEdge
    let edge = constraintEdge edgeIndex basedOn c isOriginal isGiven groups priority v1 v2
    return (mergeGraphsWithEdges False [edge] v1Node v2Node)

instance ConvertConstructor Type where
  convertConstructor = TypeConstructor

instance CanCompareTouchable Touchable Type where
  compareTouchable v tp = TypeVariable v == tp
  convertTouchable = TypeVariable
  extractTouchable (TypeVariable v) = Just v
  extractTouchable _ = Nothing
  applySubstitution sub tp = case tp of 
    TypeVariable v -> maybe (TypeVariable v) id (lookup v sub)
    TypeConstructor s -> TypeConstructor s
    TypeApplication l r -> TypeApplication (applySubstitution sub l) (applySubstitution sub r)

instance CanConvertType TestGraphM Touchable Type Constraint ConstraintInfo where
    convertType isOriginal groups priority tp = do 
      mv <- getVertexFromGraph tp
      case mv of 
        Just v -> pure (emptyTGGraph, v)
        Nothing -> f tp
      where
          f :: Type -> TestGraphM (TestGraph, VertexId)
          f (TypeConstructor n) = do
              v <- uniqueVertex
              return (singletonGraph v TGConstant{
                  constant = n
              }, v)
          f (TypeVariable v) = do
              vertexId <- uniqueVertex
              isTch <- isVertexTouchable v
              pure  (singletonGraph vertexId TGVariable{
                  variable = v,
                  representation = [show v],
                  isTouchable = isTch
              }, vertexId)
          f m@(TypeApplication l r) = do
              v <- uniqueVertex
              (lg, lv) <- convertType isOriginal groups priority l
              (rg, rv) <- convertType isOriginal groups priority r
              let vg = singletonGraph v TGApplication{
                      typeRep = m
                  }
              ei1 <- uniqueEdge
              let te1 = typeEdge ei1 0 isOriginal v lv
              ei2 <- uniqueEdge
              let te2 = typeEdge ei2 1 isOriginal v rv
              let g1 = mergeGraphsWithEdges False [te1] vg lg 
              let g2 = mergeGraphsWithEdges False [te2] rg lg
              pure (mergeGraph g1 g2, v)

instance IsTouchable TestGraphM Touchable where
  greaterTouchable t1 t2 = pure (t1 > t2)
  isVertexTouchable t = do 
        g <- getGraph
        pure (maybe Nothing isTouchable (find (\v -> getVariable v == Just (Variable t)) $ vertices g))
  setGivenTouchables touchables = do
        s <- get
        put (s{
            typeGraphEnvGivenVariables = nub (typeGraphEnvGivenVariables s ++ touchables)
        })
  getGivenTouchables = typeGraphEnvGivenVariables <$> get

instance IsEquality Type Constraint Touchable where
  isEquality (ConstraintUnify{}) = True
  splitEquality (ConstraintUnify l r) = (l, r) 
  allowInSubstitution (ConstraintUnify{}) = True

instance FreeVariables Constraint Touchable where
    getFreeVariables (ConstraintUnify l r) = getFreeVariables l ++ getFreeVariables r
    getFreeTopLevelVariables (ConstraintUnify l r) = getFreeTopLevelVariables l ++ getFreeTopLevelVariables r

instance FreeVariables Type Touchable where
    getFreeVariables (TypeVariable v) = [v]
    getFreeVariables (TypeConstructor _) = []
    getFreeVariables (TypeApplication l r) = getFreeVariables l ++ getFreeVariables r
    getFreeTopLevelVariables (TypeVariable v) = [v]
    getFreeTopLevelVariables _ = []


-- * Test graphs and dummy monad

type TestGraph = TGGraph Touchable Type Constraint ConstraintInfo

type TestGraphM = State TypeGraphEnv

instance HasGraph TestGraphM Touchable Type Constraint ConstraintInfo where
    getGraph = do
        state <- get
        pure (typeGraphEnvGraph state)
    setGraph g = do
        state <- get
        put(state{typeGraphEnvGraph = g})
    setPriority p = do
        state <- get
        put(state{typeGraphEnvCurrentPriority = p})
    getPriority = do
        state <- get
        pure (typeGraphEnvCurrentPriority state)
    ruleIsApplied r c s = do
        state <- get
        put (state{typeGraphEnvIsGraphRuleApplied = True, typeGraphEnvRulesApplied = (r, c, s) : typeGraphEnvRulesApplied state})
    isRuleApplied = typeGraphEnvIsGraphRuleApplied <$> get
    getAppliedRules = typeGraphEnvRulesApplied <$> get
    resetRuleApplied = do
        state <- get
        put (state{typeGraphEnvIsGraphRuleApplied = False, typeGraphEnvRulesApplied = []})

instance UniqueEdge TestGraphM where
    uniqueEdge = do 
      s <- get
      let curIndex = typeGraphEnvEdgeIndex s
      put (s {typeGraphEnvEdgeIndex = curIndex + 1 })
      pure curIndex
    setUniqueEdge edgeId = 
      modify (\s -> s {typeGraphEnvEdgeIndex = edgeId })

instance UniqueVertex TestGraphM where
    uniqueVertex = do 
      s <- get
      let curIndex = typeGraphEnvVertexIndex s
      put (s {typeGraphEnvVertexIndex = curIndex + 1 })
      pure curIndex
    setUniqueVertex vertexId = 
      modify (\s -> s {typeGraphEnvVertexIndex = vertexId })

instance UniqueGroup TestGraphM where
    uniqueGroup = do
        state <- get
        let curId = typeGraphEnvGroupIndex state
        put (state{typeGraphEnvGroupIndex = curId + 1})
        return curId

-- | Store the original constraints for later inspection
instance HasOriginalConstraints TestGraphM Constraint Touchable where
    setOriginalInput input = do
        state <- get
        put state{
            typeGraphEnvOriginalConstraints = input
        }
    getOriginalInput = typeGraphEnvOriginalConstraints <$> get

data TypeGraphEnv = TypeGraphEnv
  { typeGraphEnvTouchableIndex :: Int
  , typeGraphEnvEdgeIndex :: Int
  , typeGraphEnvVertexIndex :: Int
  , typeGraphEnvGroupIndex :: Int 
  , typeGraphEnvGraph :: TestGraph
  , typeGraphEnvCurrentPriority :: Int
  , typeGraphEnvIsGraphRuleApplied :: Bool
  , typeGraphEnvRulesApplied :: [(Rule, [Constraint], String)]
  , typeGraphEnvGivenVariables :: [Touchable]
  , typeGraphEnvOriginalConstraints :: ([Constraint], [Constraint], [Touchable])
  }

emptyTypeGraphEnv :: TypeGraphEnv
emptyTypeGraphEnv = TypeGraphEnv
  { typeGraphEnvTouchableIndex = 0
  , typeGraphEnvEdgeIndex = 0
  , typeGraphEnvVertexIndex = 0
  , typeGraphEnvGroupIndex = 0
  , typeGraphEnvGraph = emptyTGGraph
  , typeGraphEnvCurrentPriority = 0
  , typeGraphEnvIsGraphRuleApplied = False
  , typeGraphEnvRulesApplied = []
  , typeGraphEnvGivenVariables = []
  , typeGraphEnvOriginalConstraints = ([], [], [])
  } 

runTypeGraphM :: TestGraphM a -> a
runTypeGraphM m = evalState m emptyTypeGraphEnv