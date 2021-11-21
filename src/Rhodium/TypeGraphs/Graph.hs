{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
-- | Representing an acutal type graph
module Rhodium.TypeGraphs.Graph(
    VertexId,
    EdgeId,
    GroupId,
    Groups,
    Priority,
    TGGraph(..),
    TGVertex(..),
    TGVertexCategory(..),
    TGEdge(..),
    TGEdgeCategory(..),
    IsResolved(..),
    NodeValue(..),
    CanCompareTouchable(..),
    ConvertConstructor(..),
    RulesTried(..),
    emptyTGGraph,
    singletonGraph,
    getEdgeFromId,
    getVertexFromId,
    insertEdge,
    insertEdges,
    mergeGraph,
    mergeGraphs,
    mergeGraphsWithEdges,
    insertGraph,
    insertGraphs,
    constraintEdge,
    typeEdge,
    getVariable,
    getGroupFromEdge,
    isConstraintEdge
) where

import Control.Arrow

import Data.Maybe
import Data.Function
import Data.List
import qualified Data.Map.Strict as M

import Rhodium.Solver.Rules

import Debug.Trace

-- | The id of the vertex
type VertexId = Int
-- | The id of the edge
type EdgeId = Int

-- | The priority of an edge, usually starting at 0
type Priority = Int

-- | The id of a group
type GroupId = Int

-- | The representation of the groups to which an edge belongs, where the top level group is at the end and the deepest group is at the beginning.
type Groups = [GroupId]

-- | The main type graph data type, consisting of vertices and edges
data TGGraph touchable types constraint ci = TGGraph{
    vertices :: M.Map VertexId (TGVertexCategory touchable types),
    edges :: M.Map EdgeId (TGEdge constraint),
    typeMapping :: M.Map types VertexId,
    unresolvedConstraints :: [TGEdge constraint],
    nextUnresolvedConstraints :: [TGEdge constraint],
    resolvedErrors :: Maybe [(TGEdge constraint, ci, constraint, ErrorLabel)],
    baseGroup :: Groups
} deriving (Eq)

instance (Show touchable, Show types, Show constraint) => Show (TGGraph touchable types constraint ci) where
    show g = unlines (
        "Vertices" : map show (M.toList $ vertices g) ++ "Edges" : map show (M.toList $ edges g) ++ "Mapping" : map show (M.toList $ typeMapping g) ++ "Unresolved" : map show (unresolvedConstraints g)
        )

-- | Combines the id and the category of a vertex into a single value
newtype TGVertex touchable types = TGVertex{tgVertex :: (VertexId, TGVertexCategory touchable types)}
    deriving Show

-- | Describes the kinds of vertices that are available in type graphs
data TGVertexCategory touchable types 
    -- | A variable vertex that might be used to unify
    = TGVariable{
            variable :: touchable, -- ^The variable that might be unified
            isTouchable :: Maybe Priority, -- ^ Whether the variable can be touched
            representation :: [String]
        }
    -- | A constant type, such as @Int@ or @Bool@
    | TGConstant{
            constant :: String -- ^The name of the constant
        }
    -- | Represent the type that consists of multiple type vertices, such as an application
    | TGApplication{
            typeRep :: types -- ^ The type the vertex originally represented
        }
    | TGConstraintApplication{

        }
    | TGScopedVariable{
        typeRep :: types, -- ^ The type of the scoped variable, including the variable
        variable :: touchable
        }
    | TGDeadNode -- ^ This represents a node without a value, this can be used for constraints that only describe a single other node, like @Eq a@.
    deriving (Ord, Eq, Show)

-- | Describes an edge between the two vertices
data TGEdge constraint 
    = TGEdge{
        from :: VertexId, -- ^ The source of the edge
        to :: VertexId, -- ^ The target of the edge
        edgeId :: EdgeId, -- ^ The id of the edge, should be unique
        original :: Bool, -- ^ Whether the edge is based on an the original types or constraints
        edgeCategory :: TGEdgeCategory constraint -- ^ The kind of edge it represents
    }
    deriving (Eq)

instance Show constraint => Show (TGEdge constraint) where
    show (TGEdge from to edgeId original ec@TGConstraint{}) = concat ([
        "{"
        , show edgeId, "=>"
        ,  fixedLenghtString 2 (show from) ++ " -> " ++ fixedLenghtString 3 (show to)
        , " original? : ", show original, " "
        , " constraint : " ++ fixedLenghtString 20 (show (constraint ec))
        , " isGiven : " ++ fixedLenghtString 5 (show (isGiven ec))
        , " p: " ++ show (priority ec)
       
        
        -- , " rulesTried: " ++ show (length $ rulesTried ec)
        , " groups: " ++ show (groups ec)
        , " basedOn: " ++ show (basedOn ec)
        , " influences: " ++ show (influences ec)
        , " resolved: " ++ show (isResolved ec) ]
        ++ (case isIncorrect ec of
                Nothing -> []
                Just c -> ["incorrect: ", show c])
        ++
        [ "}"
        ])
    show (TGEdge from to edgeId original ec@TGType{}) = concat [
        "{"
        , fixedLenghtString 3 (show from) ++ " -> " ++ fixedLenghtString 3 (show to)
        , " original? : ", show original
        , "ordering : ", fixedLenghtString 2 (show (ordering ec))
        , "}"
        ]

fixedLenghtString :: Int -> String -> String
fixedLenghtString n s   | n < length s = s
                        | otherwise = fixedLenghtString n (s ++ " ") 

-- | Determines if a constraint edge is resolved
data IsResolved 
    = UnResolved -- Initial value of every edge, if the edge is not yet resolved
    | Resolved Rule [EdgeId] -- Means that the edge is resolved. This value says nothing about whether the edge was succesfully resolved, but only which rule was applied and which (other) edges are related.
    deriving (Eq, Show)

-- | The kind of the edge
data TGEdgeCategory constraint 
    -- | A constraint edge
    = TGConstraint{
        constraint :: constraint, -- ^ The original constraint
        isGiven :: Bool, -- ^ Whether the constraint is given or wanted
        isResolved :: [(Groups, IsResolved)], -- ^ Whether the constraint is resolved
        isIncorrect :: Maybe ErrorLabel, -- ^ Whether the constraint is incorrect, Nothing means unresolved or no error
        basedOn :: [EdgeId], -- ^ The list of edges on which this edge is directly based
        rulesTried :: [RulesTried],
        groups :: Groups,
        priority :: Priority, -- ^ The priority of the constraint, the lowest constraints get resolved first
        influences :: [EdgeId]
        }
    -- | An edge that links two types
    | TGType{
        ordering :: Int -- ^ The ordering between the edges that have the same parent
        }
    deriving (Eq, Show)

-- | Which rules are already applied 
data RulesTried 
        = SingleRule Rule -- ^ A rule that acts independently of others, like Canon and TopLevelReact
        | MultiRule Rule [EdgeId] -- ^ A rule, like Interact and Simplify, that acts with other edges, it stores with which edges interaction was tried
    deriving Show

instance Eq RulesTried where
    SingleRule r1 == SingleRule r2 = r1 == r2
    MultiRule r1 _ == MultiRule r2 _ = r1 == r2
    _ == _ = False

instance Eq (TGVertex touchable types) where
    v1 == v2 = fst (tgVertex v1) == fst (tgVertex v2)

instance Ord (TGVertex touchable types) where
    v1 <= v2 = fst (tgVertex v1) <= fst (tgVertex v2)
    v1 >= v2 = fst (tgVertex v1) >= fst (tgVertex v2)
    
-- | Represents an emtpy type graph without any nodes or vertices
emptyTGGraph :: TGGraph touchable types constraint ci
emptyTGGraph = TGGraph{
    vertices = M.empty,
    edges = M.empty,
    typeMapping = M.empty,
    unresolvedConstraints = [],
    nextUnresolvedConstraints = [],
    resolvedErrors = Nothing,
    baseGroup = []
}

-- | Creates a type graph with a single vertex and no edges
singletonGraph  :: CanCompareTouchable touchable types 
                => VertexId -- ^ The 'VertexId' of the vertex that needs to be inserted
                -> TGVertexCategory touchable types -- ^ The vertex category that describes the kind of edge
                -> TGGraph touchable types constraint ci -- ^ The type graph with the single vertex
singletonGraph vid vcat = emptyTGGraph{
        vertices = M.singleton vid vcat,
        typeMapping = categoryToMapping vid vcat,
        baseGroup = []
    }

categoryToMapping :: CanCompareTouchable touchable types => VertexId -> TGVertexCategory touchable types -> M.Map types VertexId
categoryToMapping vid cat = maybe M.empty (\v' -> 
    case v' of 
        Variable v -> M.singleton (convertTouchable v) vid
        _ -> M.empty
        ) (getVariable cat)


-- | Inserts an edge into the type graph
insertEdge  :: TGEdge constraint -- ^ The edge that needs to be inserted
            -> TGGraph touchable types constraint ci -- ^ The graph the edge is inserted into
            -> TGGraph touchable types constraint ci -- ^ The resulting graph
insertEdge edge g = g{
    edges = M.insert (edgeId edge) edge (edges g),
    baseGroup = if isConstraintEdge edge && (null (baseGroup g) || length (baseGroup g) > length (getGroupFromEdge edge)) then getGroupFromEdge edge else baseGroup g
}

-- | Inserts a list of edges
insertEdges :: [TGEdge constraint] -- The list of edges
            -> TGGraph touchable types constraint ci -- The source graph
            -> TGGraph touchable types constraint ci -- The resulting graph
insertEdges constraints graph = foldr insertEdge graph constraints

edgeSubstitution :: [(VertexId, VertexId)] -> TGGraph touchable types constraint ci -> TGGraph touchable types constraint ci
edgeSubstitution mapping g = let
    es = edges g

    es' = M.map (edgeSub mapping) es 
    in g{
        edges = es',
        unresolvedConstraints = map (edgeSub mapping) (unresolvedConstraints g)
    }

edgeSub :: [(VertexId, VertexId)] -> TGEdge constraint -> TGEdge constraint 
edgeSub mapping orig = let 
        origTo = to orig
        origFrom = from orig
    in orig{
        to = fromMaybe origTo (lookup origTo mapping),
        from = fromMaybe origFrom (lookup origFrom mapping)
    }


-- | Insert a graph into an exising graph, including mergin the constructors (which doesn't happen with mergeGraph)
insertGraph :: (ConvertConstructor types, Ord types, Eq constraint, Eq touchable, CanCompareTouchable touchable types) => TGGraph touchable types constraint ci -> TGGraph touchable types constraint ci -> TGGraph touchable types constraint ci
insertGraph = mergeGraphsWithEdges True []

-- | Insert a list of graphs into an existing graph, including merging the constructors
insertGraphs :: (ConvertConstructor types, Ord types, Eq constraint, Eq touchable, CanCompareTouchable touchable types) => TGGraph touchable types constraint ci -> [TGGraph touchable types constraint ci] -> TGGraph touchable types constraint ci
insertGraphs = foldr insertGraph

-- | Merge two graphs into a new graph
mergeGraph :: (ConvertConstructor types, Ord types, Eq constraint, Eq touchable, CanCompareTouchable touchable types) => TGGraph touchable types constraint ci -> TGGraph touchable types constraint ci -> TGGraph touchable types constraint ci
mergeGraph = mergeGraphsWithEdges False []

-- | Merge a list of graphs into a single graph
mergeGraphs :: (ConvertConstructor types, Ord types, Eq constraint, Eq touchable, CanCompareTouchable touchable types) => TGGraph touchable types constraint ci -> [TGGraph touchable types constraint ci] -> TGGraph touchable types constraint ci
mergeGraphs = foldr mergeGraph

-- | Merge two graphs and insert the given edges
mergeGraphsWithEdges    :: (Ord types, Eq types, Eq constraint, Eq touchable, ConvertConstructor types, CanCompareTouchable touchable types) 
                        => Bool -- ^ Whether the constant nodes from the first graph should also be merge into the second graph
                        -> [TGEdge constraint] -- ^ The edges to insert into the final graph
                        -> TGGraph touchable types constraint ci -- ^ The first source graph
                        -> TGGraph touchable types constraint ci -- ^ The second source graph
                        -> TGGraph touchable types constraint ci -- ^ The resulting graph
mergeGraphsWithEdges combineConstants es g1 g2 = let
        v1 = vertices g1
        v2 = vertices g2
        g2Mapping = typeMapping g2 `M.union` constructTypeMapping g2
        v12Mapping = M.elems $ M.intersectionWith (\v1 v2 -> (v2, v1)) (typeMapping g1) g2Mapping
        nv = M.filterWithKey (\k _ -> k `notElem` map fst v12Mapping) v2
        g2' = edgeSubstitution v12Mapping g2
    in TGGraph{
            vertices = v1 `M.union` nv,
            edges = M.map (edgeSub v12Mapping) (M.fromList (map (\e -> (edgeId e, e)) es)) `M.union` edges g1 `M.union` edges g2',
            typeMapping = typeMapping g1 `M.union ` g2Mapping,
            unresolvedConstraints = unresolvedConstraints g1 ++ unresolvedConstraints g2',
            nextUnresolvedConstraints = [],
            resolvedErrors = case (resolvedErrors g1, resolvedErrors g2) of
                (Just re1, Just re2) -> Just (re1 ++ re2)
                (Just re, _) -> Just re
                (_, Just re) -> Just re
                _ -> Nothing,
            baseGroup = baseGroup g1
        }
-- | The possible values of a node
data NodeValue touchable types = Variable touchable | Constant String | Type types | Dead deriving Eq

constructTypeMapping :: (Ord types, ConvertConstructor types, CanCompareTouchable touchable types) => TGGraph touchable types constraint ci -> M.Map types VertexId 
constructTypeMapping g = M.fromList $ mapMaybe (\(v, vc) -> 
    case vc of 
        TGConstant c -> Just (convertConstructor c, v)
        vc@TGVariable{} -> Just (convertTouchable (variable vc), v)
        ta@TGApplication{} -> Just (typeRep ta, v)
        TGConstraintApplication{} -> Nothing
        TGDeadNode{} -> Nothing
        sv@TGScopedVariable{} -> Just (typeRep sv, v)
    ) $ M.toList (vertices g)
                                   

-- | Get a touchable from a category, if the touchable exists
getVariable :: TGVertexCategory touchable types -> Maybe (NodeValue touchable types)
getVariable v@TGVariable{} = Just (Variable $ variable v)
getVariable v@TGDeadNode{} = Just Dead
getVariable _              = Nothing

-- | Creates a new edge based on a constraint
constraintEdge  :: EdgeId -- ^ The id of the edge
                -> [EdgeId] -- ^ The list of the edges this edge was based on
                -> constraint -- ^ The constraint this edge represents
                -> Bool -- ^ Whether the constraint was original 
                -> Bool -- ^ Whether the constraint is given or wanted
                -> Groups
                -> Priority
                -> VertexId -- ^ The source vertex id
                -> VertexId -- ^ The target vertex id
                -> TGEdge constraint -- ^ The resulting edge
constraintEdge edgeId parents constraint original isGiven gs priority from to = TGEdge{
        from = from,
        to = to,
        edgeId = edgeId,
        original = original,
        edgeCategory = TGConstraint{
            constraint = constraint,
            isGiven = isGiven,
            isResolved = [(gs, UnResolved)],
            isIncorrect = Nothing,
            basedOn = parents,
            rulesTried = [],
            groups = gs,
            priority = priority,
            influences = []
        }
    }

-- | Constructs a type edge between two vertices
typeEdge    :: EdgeId -- ^ The edge id
            -> Int -- ^ The ordering between the types
            -> Bool -- ^ whether the edge was original
            -> VertexId -- ^ The source vertex id
            -> VertexId -- ^ The target vertex id
            -> TGEdge constraint -- ^ The resulting constraint
typeEdge edgeId ordering original from to = TGEdge{
        from = from,
        to = to,
        edgeId = edgeId,
        original = original,
        edgeCategory = TGType{
            ordering = ordering
        }
    }


getChildNodes   :: TGGraph touchable types constraint ci
                -> VertexId
                -> [VertexId]
getChildNodes graph v = getChildNodes' [] v ++ parentNode v
    where 
        parentNode :: VertexId -> [VertexId]
        parentNode cv = let
            upEdges = filter (\e -> isTypeEdge e && to e == cv) (M.elems $ edges graph)
            parents = filter (\(_, e) -> isApplication e || isDeadNode e) $ map ((`getVertexFromId` graph) . from) upEdges
            in if null parents then [cv] else concatMap (parentNode . fst) parents
        getChildNodes' found v = 
            let
                downEdges = filter (\e -> isTypeEdge e && from e == v) (M.elems $ edges graph)
            in v : concatMap (getChildNodes' (v : found)) (map to downEdges \\ (v:found))


isApplication :: TGVertexCategory touchable types -> Bool
isApplication TGApplication{} = True
isApplication TGConstraintApplication{} = True
isApplication _ = False
            
isDeadNode :: TGVertexCategory touchable types -> Bool
isDeadNode TGDeadNode{} = True
isDeadNode _ = False

        
-- | Retrieves a vertex from the graph by id
getVertexFromId :: VertexId -> TGGraph touchable types constraint ci -> (VertexId, TGVertexCategory touchable types)
getVertexFromId vi graph = maybe (error $ "Unknown vertex id: " ++ show vi) (\vc -> (vi, vc)) (M.lookup vi (vertices graph))

getVerticesFromId :: [VertexId] -> TGGraph touchable types constraint ci -> [(VertexId, TGVertexCategory touchable types)]
getVerticesFromId vis graph = map (`getVertexFromId` graph) vis

-- | Returns the first matching edge with the provided id
getEdgeFromId :: TGGraph touchable types constraint ci -> EdgeId -> TGEdge constraint
getEdgeFromId graph id = fromMaybe (error "Unknown edge id") (M.lookup id (edges graph))

isTypeEdge :: TGEdge constraint -> Bool
isTypeEdge TGEdge{edgeCategory = TGType{}} = True
isTypeEdge _ = False

-- | The touchable and the type can be compared to be equal
class CanCompareTouchable touchable types | types -> touchable where
    -- | Compare the touchable and the type whether they should be considered equal
    compareTouchable :: touchable -> types -> Bool
    -- | Convert a touchable to a type
    convertTouchable :: touchable -> types

    extractTouchable :: types -> Maybe touchable

    applySubstitution :: [(touchable, types)] -> types -> types

-- | Convert the string into a type in case of a constructor
class ConvertConstructor types where
    -- | Convert a string into a constructor
    convertConstructor :: String -> types

-- | Get the group from a (constraint) edge
getGroupFromEdge :: TGEdge constraint -> Groups 
getGroupFromEdge TGEdge{edgeCategory = ec@TGConstraint{}} = groups ec
getGroupFromEdge _ = error "Only constraint edges have a group"

-- | Checks whether an edge is a constraint edge
isConstraintEdge :: TGEdge constraint -> Bool
isConstraintEdge TGEdge{edgeCategory = TGConstraint{}} = True
isConstraintEdge _ = False