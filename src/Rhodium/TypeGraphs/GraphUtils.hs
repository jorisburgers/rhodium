{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MonoLocalBinds #-}
-- | Provides a number of functions on TypeGraphs
module Rhodium.TypeGraphs.GraphUtils where

import Rhodium.TypeGraphs.Graph
    ( CanCompareTouchable (..)
    , EdgeId
    , Groups
    , IsResolved(..)
    , Priority
    , RulesTried (..)
    , TGEdge (..)
    , TGEdgeCategory (..)
    , TGGraph (..)
    , TGVertexCategory (..)
    , VertexId
    , isConstraintEdge
    , getGroupFromEdge 
    , getEdgeFromId
    , getVertexFromId
    )
import Rhodium.TypeGraphs.GraphProperties 
    ( CompareTypes (..)
    , FreeVariables (..)
    , HasConstraintInfo (..)
    , HasGraph (..)
    , HasTypeGraph
    , IsEquality (..)
    , getGraph
    )
import Rhodium.Solver.Rules (Rule (..), ErrorLabel (..), labelResidual)

import qualified Data.Map.Strict as M

import Data.List (nub, isSuffixOf, sortBy, intersect, delete)
import Data.Maybe (mapMaybe, isJust, fromMaybe, catMaybes)
import Data.Function (on)

import Control.Arrow (second)

-- | Checks whether an adge is a type edge
isTypeEdge :: TGEdge constraint -> Bool
isTypeEdge TGEdge{edgeCategory = TGType{}} = True
isTypeEdge _ = False

-- | Get the category from the edge
getEdgeCategory :: TGEdge constraint -> TGEdgeCategory constraint
getEdgeCategory TGEdge{edgeCategory = ec} = ec

-- | Get if an edge is incorrect
getIsIncorrect :: TGEdge constraint -> Maybe ErrorLabel
getIsIncorrect TGEdge{edgeCategory = TGConstraint{isIncorrect = sIncorrect}} = sIncorrect
getIsIncorrect _ = error "Edge is not a constraint edge"

-- | Get if and how a constraint edge is resolved
getResolved :: Groups -> TGEdge constraint -> IsResolved
getResolved groups' edge@TGEdge{edgeCategory = TGConstraint{}} = fromMaybe UnResolved $ lookup groups' $ isResolved (edgeCategory edge)
getResolved _ _ = error "Not a constraint edge"

-- | Checks whether an edge is given (or wanted)
isEdgeGiven :: TGEdge constraint -> Bool
isEdgeGiven TGEdge{edgeCategory = ec@TGConstraint{}} = isGiven ec
isEdgeGiven _ = error "Only constraint edges can be given"

-- | Check if the edge is an original edge
isEdgeOriginal :: TGEdge constraint -> Bool
isEdgeOriginal = original

-- | Get the original constraint from an edge
getConstraintFromEdge :: Show constraint => TGEdge constraint -> constraint
getConstraintFromEdge TGEdge{edgeCategory = ec@TGConstraint{}} = constraint ec
getConstraintFromEdge x = error $ "Edge doesn't have a constraint" ++ show x

-- | Marks an edge as incorrect
makeIncorrect   :: Eq constraint 
                => ErrorLabel -- ^ Which label is given to the error
                -> TGEdge constraint -- ^ What edge should mark
                -> TGGraph touchable types constraint ci -- ^ The graph the edge is in
                -> TGGraph touchable types constraint ci -- ^ The resulting graph
makeIncorrect el edge g = 
        g{
            edges = M.adjust (\e -> 
                e{ edgeCategory = (edgeCategory edge){
                    isIncorrect = Just el
                }}) (edgeId edge) (edges g),
            unresolvedConstraints = delete edge (unresolvedConstraints g)
        }

-- | Mark an edge as resolved
markEdgeResolved    :: (Eq constraint) 
                    => Groups
                    -> IsResolved -- ^ Indicates that and how the edge is resolved 
                    -> TGEdge constraint -- ^ The edge that is resolved
                    -> TGGraph touchable types constraint ci -- ^ The graph the edge is in
                    -> TGGraph touchable types constraint ci -- ^ The resulting graph
markEdgeResolved groups' ir edge g = g{
        edges = M.adjust (\e -> e{ edgeCategory = (edgeCategory e){
            isResolved = (groups', ir) : filter ((groups' /=) . fst) (isResolved (edgeCategory e))
            }}) (edgeId edge) (edges g),
        unresolvedConstraints = delete edge (unresolvedConstraints g)
    }

-- | Mark that an edge is tried, maybe in combination with some other edges.
markEdgeTried :: RulesTried -> TGEdge constraint -> TGGraph touchable types constraint ci -> TGGraph touchable types constraint ci
markEdgeTried rt e' g = g{
        edges = M.adjust (\e -> e{
            edgeCategory = (edgeCategory e){
                rulesTried = 
                    let 
                        alreadyTried = rulesTried (edgeCategory e)
                        rt' = mergeRules alreadyTried
                        mergeMR ms (MultiRule r ms') = MultiRule r (ms' ++ ms)
                        mergeMR _ _ = error "Cannot merge single rule"
                        mergeRules [] = [rt]
                        mergeRules (x@(SingleRule _) : xs)   
                            | x == rt = x : xs
                            | otherwise = x : mergeRules xs
                        mergeRules (x@(MultiRule _ m) : xs)   
                            | x == rt = mergeMR m rt : xs
                            | otherwise = x : mergeRules xs                      
                in rt'}
        }) (edgeId e') (edges g)
    }

-- | Return the edges that were used in a multirule.
getEdgesFromMultirule :: RulesTried -> [EdgeId]
getEdgesFromMultirule (MultiRule _ xs) = xs
getEdgesFromMultirule (SingleRule _) = error "Cannot get edges from single rule"

-- | Return a list of edges that are not yet resolved
getUnresolvedConstraintEdges :: Show constraint => Groups -> TGGraph touchable types constraint ci -> [TGEdge constraint]
getUnresolvedConstraintEdges groups' graph = filter (isUnresolvedConstraintEdge groups') (M.elems $ edges graph)

-- | Get all the unresolved constraint from a graph
getUnresolvedConstraintEdges' :: TGGraph touchable types constraint ci -> [TGEdge constraint]
getUnresolvedConstraintEdges' g = filter isUnresolvedConstraintEdge' (M.elems $ edges g)

-- | Get all the unresolved constraints from a given priority
getUnresolvedConstraintEdgesByPriority :: Show constraint => Priority -> TGGraph touchable types constraint ci -> [TGEdge constraint]
getUnresolvedConstraintEdgesByPriority p graph = concatMap (`getUnresolvedConstraintEdges` graph) $ getGroupsByPriority p graph

-- | Get all the groups from a graph by priority
getGroupsByPriority :: Priority -> TGGraph touchable types constraint ci -> [Groups]
getGroupsByPriority p g = nub $ map getGroupFromEdge $ filter (\e -> isConstraintEdge e &&  getPriorityFromEdge e == p ) $ M.elems $ edges g

-- | Determine whether a constraint is involved in an error. In such a case the simplifier will not allow a constraint to be used in simplification to ensure termination.
isInvolvedInError :: (Show constraint, FreeVariables constraint touchable, Eq touchable)=> TGEdge constraint -> TGGraph touchable types constraint ci -> Bool
isInvolvedInError edge g = let
    es = filter (\e -> isConstraintEdge e && isJust (getIsIncorrect e)) $ M.elems (edges g)
    errorVars = nub $ concatMap (getFreeTopLevelVariables . getConstraintFromEdge) es
    consVars = nub $ getFreeTopLevelVariables $ getConstraintFromEdge edge
    in not (null (errorVars `intersect` consVars)) 

-- | Gets the path for an edge how it was constructed
getPath :: (Show constraint, Eq constraint) => TGGraph touchable types constraint ci -> TGEdge constraint -> [TGEdge constraint]
getPath graph edge@TGEdge{edgeCategory=tgc@TGConstraint{}}  
                    | isEdgeOriginal edge = [edge]
                    | otherwise = let xs = nub $ concatMap (getPath graph . getEdgeFromId graph) (basedOn tgc) in if null xs then error (show ("Empty", edge)) else xs
getPath _ _ = error "Trying to get a path from a non-constraint edge"

-- | Get the influences from an edge
getInfluences :: TGGraph touchable types constraint ci -> EdgeId -> [EdgeId]
getInfluences g e = e : concatMap (getInfluences g) (influences (edgeCategory (getEdgeFromId g e)))

-- | Get the edge ids that are resolvers of an edge
getResolvers :: TGGraph touchable types constraint ci -> EdgeId -> [EdgeId]
getResolvers g e = nub $ e : concatMap (getResolvers g) (delete e $ concatMap getResolver $ isResolved (edgeCategory (getEdgeFromId g e)))

-- | Get the resolver from a IsResolved data type
getResolver :: (Groups, IsResolved) -> [EdgeId]
getResolver (_, UnResolved) = []
getResolver (_, Resolved _ eids) = eids


-- | Check wether the constraint is touchable
isConstraintTouchable :: (Show touchable, Show types, Show constraint) => Priority -> TGGraph touchable types constraint ci -> TGEdge constraint -> Bool
isConstraintTouchable p g e = let
    isVariable TGVariable{} = True
    isVariable _ = False
    (_, v1) = getVertexFromId (from e) g
    (_, v2) = getVertexFromId (to e) g
    in case (isVariable v1, isVariable v2) of
            (False, False) -> True
            (True, False) -> isTouchable v1 == Just p || (odd p && isTouchable v1 == Just (p - 1) ) || (even p && isTouchable v1 == Just (p + 1))
            (False, True) -> isTouchable v2 == Just p || (odd p && isTouchable v2 == Just (p - 1) ) || (even p && isTouchable v2 == Just (p + 1))
            (True, True) -> (isTouchable v1 == Just p) || 
                            (isTouchable v2 == Just p) || 
                            (odd p && isTouchable v1 == Just (p - 1) ) || 
                            (odd p && isTouchable v2 == Just (p - 1) ) || 
                            (even p && isTouchable v1 == Just (p + 1)) || 
                            (even p && isTouchable v2 == Just (p + 1))

-- | Get the vertex that represents the given type
getVertexFromGraph :: (Monad m, Ord types, HasGraph m touchable types constraints ci) => types -> m (Maybe VertexId)
getVertexFromGraph t = do
    g <- getGraph
    let mapping = typeMapping g
    return (M.lookup t mapping)

-- | Calculate the maximum priority that is in a graph
maxGraphPriority :: TGGraph touchable types constraint ci -> Priority
maxGraphPriority g = maximum $ map (priority . edgeCategory) $ filter isConstraintEdge $ M.elems $ edges g


-- | Return the priority from a (constraint) edge
getPriorityFromEdge :: TGEdge constraint -> Priority 
getPriorityFromEdge TGEdge{edgeCategory = ec@TGConstraint{}} = priority ec
getPriorityFromEdge _ = error "Only constraint edges have a priority"

-- | Determine whether whether the first group is a subset or equal to the second group.
sameGroups :: Groups -> Groups -> Bool
sameGroups = isSuffixOf

-- | Return the longest group from the two edges. One of the edges should be a suffix of the other.
maxGroup :: TGEdge constraint -> TGEdge constraint -> Groups
maxGroup c1 c2 = let 
                    g1 = getGroupFromEdge c1
                    g2 = getGroupFromEdge c2
                in if length g1 > length g2 then g1 else g2

-- | Get the maximum priority between two edges, which is the highest priority unless one edge is equal to the given edge. This can happen with the interact rule, where the same rule is returned.
maxPriority :: (Eq constraint, Show constraint) => constraint -> TGEdge constraint -> TGEdge constraint -> Priority
maxPriority orig c1 c2  | getConstraintFromEdge c1 == orig = getPriorityFromEdge c1
                        | getConstraintFromEdge c2 == orig = getPriorityFromEdge c2
                        | otherwise = max (getPriorityFromEdge c1) (getPriorityFromEdge c2)

-- | Mark an edge with the given influenced edges
markInfluences  :: [EdgeId] -- ^ The edges that influenced the creation of the current edge
                -> EdgeId -- The current edge
                -> TGGraph touchable types constraint ci 
                -> TGGraph touchable types constraint ci
markInfluences inf e g = g{
        edges = M.adjust (\ec -> ec{
                edgeCategory = (edgeCategory ec){
                    influences = inf ++ influences (edgeCategory ec)
                }
            }) e (edges g)
    } 

-- | Mark that the given edges influence the creation of the new edges
markInfluencesEdges :: [EdgeId] -- ^The edges that the current edges are based upon
                    -> [EdgeId] -- ^The edges that were given
                    -> TGGraph touchable types constraint ci
                    -> TGGraph touchable types constraint ci
markInfluencesEdges inf es g = foldr (markInfluences inf) g es

-- | Get all the groups from the 
getGroupsFromGraph :: TGGraph touchable types constraint ci -> [Groups]
getGroupsFromGraph g = nub $ concatMap (\e -> [getGroupFromEdge e | isConstraintEdge e]) (M.elems $ edges g)

-- | Checks whether an edge is unresolved in the given group
isUnresolvedConstraintEdge :: Show constraint => Groups -> TGEdge constraint -> Bool
isUnresolvedConstraintEdge groups' edge@TGEdge{edgeCategory = TGConstraint{}} = isUnresolved' (isResolved (edgeCategory edge)) groups'
                                        where
                                            isUnresolved' _ [] = False
                                            isUnresolved' res group@(_:gs) = maybe (isUnresolved' res gs) (== UnResolved) (lookup group res)
isUnresolvedConstraintEdge _ _ = False

-- | Determine whether a constraint is unresolved in any group
isUnresolvedConstraintEdge' :: TGEdge constraint -> Bool
isUnresolvedConstraintEdge' edge@TGEdge{edgeCategory = TGConstraint{}} = any ((\x -> UnResolved == x || isSub x) . snd) $ isResolved (edgeCategory edge)
                                            where
                                                isSub (Resolved Substitution _) = True
                                                isSub _ = False
isUnresolvedConstraintEdge' _ = False

-- | Checks whether an edge is unresolved in the given group
isUnresolvedConstraintEdgeSub :: Groups -> TGEdge constraint -> Bool
isUnresolvedConstraintEdgeSub groups' edge@TGEdge{edgeCategory = TGConstraint{}} = isUnresolved' (isResolved (edgeCategory edge)) groups'
                                        where
                                            isUnresolved' _ [] = False
                                            isUnresolved' res group@(_:gs) = maybe (isUnresolved' res gs) (\x -> UnResolved == x || isSub x) (lookup group res)
                                            isSub (Resolved Substitution _) = True
                                            isSub _ = False
isUnresolvedConstraintEdgeSub _ _ = False



-- | Check if the edge is residual in the specific group
isResidual :: (Show touchable, Show types, Show constraint, IsEquality types constraint touchable) => Groups -> TGGraph touchable types constraint ci -> TGEdge constraint -> Bool 
isResidual gr g e = odd (getPriorityFromEdge e) && not (isEdgeGiven e) && isUnresolvedConstraintEdge gr e && (isIncorrect (edgeCategory e) == Just labelResidual || (
    case (allowInSubstitution (getConstraintFromEdge e), isConstraintTouchable 0 g e ||  isConstraintTouchable 1 g e) of
        (False, _) -> True 
        (True, False) -> True
        (True, True) -> False
    ))

-- | Mark the edges unresolved with respect to the specific group
markEdgesUnresolved :: Show constraint => Groups -> TGGraph touchable types constraint ci -> TGGraph touchable types constraint ci
markEdgesUnresolved group g = g{
        unresolvedConstraints = getUnresolvedConstraintEdges group g
    }

-- | Return a list with the possible types for an type
getPossibleTypes :: (Show touchable, Show constraint, Show types, Monad m, Eq types, IsEquality types constraint touchables, HasGraph m touchable types constraint ci, CanCompareTouchable touchables types) => Groups -> types -> m [(types, TGEdge constraint)]
getPossibleTypes groups' t = getGraph >>= \graph -> return (mapMaybe (\e -> 
        let 
            constraint' = getConstraintFromEdge e
            (t1, t2) = splitEquality (getConstraintFromEdge e)
        in case (isEquality constraint', t1 == t, t2 == t) of 
            (False, _, _) -> Nothing
            (_, True, False) -> Just (t2, e)
            (_, False, True) -> Just (t1, e)
            _ -> Nothing
        ) (filter (\e -> isConstraintEdge e && (null groups' || groups' == getGroupFromEdge e))$ M.elems $ edges graph))
        
-- | Get the substituted type of the given type
getSubstType1 :: (CompareTypes m types, HasTypeGraph m axiom touchable types constraint ci) => types -> m types
getSubstType1 = getSubstTypeFull [0]

-- | Get the substituted type of the given type
getSubstTypeFull :: (CompareTypes m types, HasTypeGraph m axiom touchable types constraint ci) => Groups -> types -> m types
getSubstTypeFull groups' types = do
    let typeFV = getFreeVariables types
    fvSub <- catMaybes <$> mapM 
            (\fv ->     getPossibleTypes groups' (convertTouchable fv) >>= 
                \pt -> 
                    if length pt == 1 then 
                        return $ Just (fv, fst $ head pt) 
                    else if length pt > 1 then
                        let 
                            pt' = map (\(t, e) -> (t, (e, influences $ edgeCategory e))) pt
                            ptf = filter (\(_, (e, inf)) -> null (inf `intersect ` map (edgeId . fst . snd) pt') && isUnresolvedConstraintEdge' e) pt' 
                        in 
                    if length ptf > 1 then 
                        let 
                            val t = maybe (length $ getFreeVariables t) (const maxBound) (extractTouchable t)
                            ptf2 = nub $ sortBy (compare `on` val) $ map fst ptf
                        in return $ Just (fv, head ptf2)
                        else (if null ptf then 
                            let
                                vfpt = filter (\(v, _) -> 
                                        case getFreeVariables v of 
                                            [fv'] -> convertTouchable fv' /= v
                                            _ -> True
                                        ) pt'
                            in mgu (map fst vfpt) >>= (\v -> return $ Just (fv, v))
                        else
                            return $ Just (fv, head (map fst ptf)))
                    else
                        return Nothing
                            
            ) typeFV 
    graph <- getGraph
    let givenSub = mapMaybe (\e ->  let 
                    cons = getConstraintFromEdge e
                    (t1, t2) = splitEquality cons
                in case (extractTouchable t1, extractTouchable t2) of
                    (Nothing, Nothing) -> Nothing
                    (Nothing, Just v2) -> Just (v2, t1)
                    (Just v1, _) -> Just (v1, t2)
                ) $ filter (\e -> isConstraintEdge e && isGiven (edgeCategory e) && isEquality (getConstraintFromEdge e) && (null groups' || groups' == getGroupFromEdge e)) $ M.elems $ edges graph
    
    return $ applySubstitution (getSubstitutionFromGraph groups' graph) $ applySubstitution (graphToSubstition groups' graph) $ applySubstitution givenSub $ applySubstitution fvSub types

isVertexVariable :: Priority -> TGVertexCategory touchable types -> Bool
isVertexVariable p v@TGVariable{}   = isJust (isTouchable v) && isTouchable v <= Just p
isVertexVariable _ _                = False

getSubstitutionFromGraph :: (Eq types, IsEquality types constraint touchable, CanCompareTouchable touchable types, Show touchable, Show types, Show constraint) => Groups -> TGGraph touchable types constraint ci -> [(touchable, types)]
getSubstitutionFromGraph group graph = let
        prior   | null group    = 1
                | otherwise     = (length group - 1) * 2 + 1
        touchables = M.elems $ M.map variable $ M.filter (isVertexVariable prior) (vertices graph)
        initialSub = map (\t -> (t, convertTouchable t)) touchables
        mtVars = map convertTouchable touchables
        unifyC = map getConstraintFromEdge 
                    $ filter 
                        (\e -> isConstraintEdge e 
                            && allowInSubstitution (getConstraintFromEdge e) 
                            && getGroupFromEdge e `isSuffixOf` group 
                            && let
                                    (v, _) = splitEquality (getConstraintFromEdge e) 
                                in v `elem` mtVars && isJust (extractTouchable v)
                        ) 
                    $ M.elems (edges graph)
        finalSub = map (\c -> let 
                (v, m) = splitEquality c
            in (fromMaybe (error "Could not extract touchable") (extractTouchable v), m)) unifyC
    in map (second (applySubstitution finalSub)) initialSub


-- | Convert the graph to a substitution
graphToSubstition 
    :: (Eq touchable, Eq types, IsEquality types constraint touchable, Show constraint, Show types, Show touchable, CanCompareTouchable touchable types) 
    => Groups 
    -> TGGraph touchable types constraint ci 
    -> [(touchable, types)]
graphToSubstition groups' g = nub $ mapMaybe (\e ->
        if isConstraintEdge e && isEquality (getConstraintFromEdge e) && (null groups' || getGroupFromEdge e == groups') then
            let 
                (m1, m2) = splitEquality (getConstraintFromEdge e)
                v1 = extractTouchable m1                     
            in (\v -> (v, m2)) <$> v1
        else
            Nothing
    )
    (
        filter (isUnresolvedConstraintEdgeSub groups') $ M.elems $ edges g
    )

-- | Update the constraint information at the given edges
updateConstraintInformation :: HasConstraintInfo constraint ci => [(EdgeId, ci)] -> TGGraph touchable types constraint ci -> TGGraph touchable types constraint ci
updateConstraintInformation eci ginitial = foldr addCi ginitial eci 
        where
            addCi (eid, ci) g = g{
                    edges = M.adjust (\e -> e{
                            edgeCategory = (edgeCategory e){
                                    constraint = setConstraintInfo ci (constraint $ edgeCategory e)
                                }
                        }) eid (edges g)
                }
-- | Get all the neighbours from an edge id
getNeighbours :: (HasTypeGraph m axiom touchable types constraint ci) => EdgeId -> m [TGEdge constraint]
getNeighbours eid = do
    graph <- getGraph
    let es = M.elems $ edges graph
    return $ nub (filter (\e -> from e == eid || to e == eid) es)

-- | Return all edges with a specific constraints (both given and wanted)
getEdgesWithConstraint :: (Show constraint, Eq constraint) => TGGraph touchable types constraint ci -> constraint -> [EdgeId]
getEdgesWithConstraint g c = map edgeId $ filter (\e -> isConstraintEdge e && getConstraintFromEdge e == c) (M.elems $ edges g)