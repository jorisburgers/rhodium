{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MonoLocalBinds #-}
-- | Simplification algorithm of OutsideIn(X)
module Rhodium.Solver.Simplifier(simplifyGraph) where

import Prelude hiding (interact)

import Data.Maybe
import Data.List (partition, nub, isSuffixOf, (\\))

import Control.Monad

import Rhodium.Solver.Rules
import Rhodium.TypeGraphs.Graph
import Rhodium.TypeGraphs.GraphUtils
import Rhodium.TypeGraphs.GraphProperties
import Rhodium.TypeGraphs.Touchables


-- | Simplify a given graph
simplifyGraph :: (HasTypeGraph m axiom touchable types constraint ci) => Bool -> TGGraph touchable types constraint ci -> m(TGGraph touchable types constraint ci)
simplifyGraph ignoreTouchable graph = foldM (\g group -> simplifyGraph' ignoreTouchable group 0 g) graph (getGroupsFromGraph graph) 

-- | Simplify a graph starting at a group and a priority
simplifyGraph' :: (HasTypeGraph m axiom touchable types constraint ci) => Bool -> Groups -> Priority -> TGGraph touchable types constraint ci -> m(TGGraph touchable types constraint ci)
simplifyGraph' ignoreTouchable groups' priority' g = do
    resetRuleApplied
    setGraph g
    setPriority priority'
    gCanon      <- applyRule priority' Canon applyCanonRule $ markEdgesUnresolved groups' g
    gInteract   <- applyRule priority' Interact (applyInteractRule groups' priority' ) $ markEdgesUnresolved groups' gCanon
    gSimplify   <- applyRule priority' Simplify (applySimplifyRule groups' priority' ) $ markEdgesUnresolved groups' gInteract
    gReact      <- applyRule priority' TopLevelReact (applyTopLevelReactRule groups' ) $ markEdgesUnresolved groups' gSimplify
    let gFinal = gReact
    final <- isRuleApplied
    if final then 
        -- Fallback, if this is reached, something went wrong
        if length (edges gFinal) > 9999 then 
            error $ show gFinal
        else
            simplifyGraph' ignoreTouchable groups' priority' $ markEdgesUnresolved groups' gFinal
    else if priority' < maxGraphPriority gFinal then do
        g' <- resolvePriorityConstraints ignoreTouchable groups' priority' gFinal
        simplifyGraph' ignoreTouchable groups' (priority' + 1) (markEdgesUnresolved groups' g')
    else do 
        g' <- resolvePriorityConstraints ignoreTouchable groups' priority' gFinal
        return (markEdgesUnresolved groups' g')


applyRule   :: (HasTypeGraph m axiom touchable types constraint ci) 
            => Priority 
            -> Rule 
            -> (EdgeId -> TGGraph touchable types constraint ci -> m (TGGraph touchable types constraint ci)) 
            -> TGGraph touchable types constraint ci 
            -> m (TGGraph touchable types constraint ci)
applyRule prior r f g = do
    setGraph g
    let (mc, g') = nextConstraint prior r g
    case mc of 
        Nothing -> return g'{
                nextUnresolvedConstraints = [],
                unresolvedConstraints = nextUnresolvedConstraints g'
            }
        Just c -> f (edgeId c) g' >>= applyRule prior r f

nextConstraint :: Show constraint => Priority -> Rule -> TGGraph touchable types constraint ci -> (Maybe (TGEdge constraint), TGGraph touchable types constraint ci)
nextConstraint prior r g =
    case unresolvedConstraints g of 
        [] -> (Nothing, g)
        (x:xs)  | (prior /= priority (edgeCategory x) && r /= Simplify) || SingleRule r `elem` rulesTried (edgeCategory x) -> nextConstraint prior r g{unresolvedConstraints = xs}
                | otherwise -> (Just x, g{unresolvedConstraints = xs})

addUnresolvedConstraints :: [TGEdge constraint] -> TGGraph touchable types constraint ci -> TGGraph touchable types constraint ci
addUnresolvedConstraints cs g = g{
        nextUnresolvedConstraints = cs ++ nextUnresolvedConstraints g
    }

applyCanonRule :: (HasTypeGraph m axiom touchable types constraint ci) => EdgeId -> TGGraph touchable types constraint ci -> m(TGGraph touchable types constraint ci)
applyCanonRule edgeIndex graph = do
    let edge = getEdgeFromId graph edgeIndex
    result <- canon (isEdgeGiven edge) (getConstraintFromEdge edge)
    let graph' = markEdgeTried (SingleRule Canon) edge graph
    if not (isErrorResult result) then
            if isJust (isApplied result) then do
                let (touchables, _subsitution, constraints) = fromJust (isApplied result)
                let graph'' = markEdgeResolved (getGroupFromEdge edge) (Resolved Canon [edgeId edge]) edge graph'
                ruleIsApplied Canon [getConstraintFromEdge edge] (show result)
                applyCanonResult edge touchables constraints graph''
            else
                return graph'
        else
            return $ markEdgeResolved (getGroupFromEdge edge) (Resolved Canon [edgeId edge]) edge $ makeIncorrect (getErrorLabel result) edge graph'
            

applyCanonResult :: (HasTypeGraph m axiom touchable types constraint ci) => TGEdge constraint -> [touchable] -> [constraint] -> TGGraph touchable types constraint ci -> m(TGGraph touchable types constraint ci)
applyCanonResult edge touchables constraints graph = do 
    constraints' <- mapM (convertConstraint [edgeId edge] False (isEdgeGiven edge) (groups (edgeCategory edge)) (priority (edgeCategory edge))) constraints
    let graph' = insertGraphs graph constraints'
    let newEdges = concatMap getUnresolvedConstraintEdges' constraints'
    when (isEdgeGiven edge) (setGivenTouchables touchables)
    return
        $ addUnresolvedConstraints newEdges
        $ markInfluencesEdges (map edgeId newEdges) [edgeId edge] 
        $ markTouchables (map (\v -> (v, priority $ edgeCategory edge)) touchables) graph'

applyInteractRule :: (HasTypeGraph m axiom touchable types constraint ci) => Groups -> Priority -> EdgeId -> TGGraph touchable types constraint ci -> m(TGGraph touchable types constraint ci)    
applyInteractRule groups' curPrior edgeIndex graph = do
    let edge = getEdgeFromId graph edgeIndex
    let doneEdges = concatMap getEdgesFromMultirule $ filter (MultiRule Interact [] ==) (rulesTried $ edgeCategory edge)
    candidateEdges <- getInteractionCandidates doneEdges edge graph
    let graph' = markEdgeTried (MultiRule Interact $ map edgeId candidateEdges) edge graph
    foldM (\g ei -> do 
            
            let e = getEdgeFromId g ei
            let edge' = getEdgeFromId g edgeIndex
            setGraph g
            if      isUnresolvedConstraintEdge groups' e 
                &&  isUnresolvedConstraintEdge groups' edge' 
                &&  edgeId e /= edgeId edge' 
                &&  getGroupFromEdge edge' == groups'
                &&  (getGroupFromEdge e `isSuffixOf` getGroupFromEdge edge' || getGroupFromEdge edge' `isSuffixOf` getGroupFromEdge e)
                &&  (   priority (edgeCategory edge) == priority (edgeCategory e)
                    ||  (getPriorityFromEdge edge' < curPrior && getPriorityFromEdge e < curPrior)
                    ||  (even curPrior && getPriorityFromEdge edge' <= curPrior && getPriorityFromEdge e <= curPrior)
                    )
                
            then if length (getGroupFromEdge e) == length (getGroupFromEdge edge) && getGroupFromEdge e /= getGroupFromEdge edge' then error $ show (e, edge) else do
                result <- interact (isEdgeGiven edge) (getConstraintFromEdge edge) (getConstraintFromEdge e)
                applyInteractResult edge' (e, result) g
            else
                return g
        ) graph' (map edgeId candidateEdges)

applyInteractResult :: (HasTypeGraph m axiom touchable types constraint ci) => TGEdge constraint -> (TGEdge constraint, RuleResult [constraint]) -> TGGraph touchable types constraint ci -> m (TGGraph touchable types constraint ci)
applyInteractResult edge (e, Error label) graph = let
    !g1 = makeIncorrect label edge graph
    !g2 = markEdgeResolved (getGroupFromEdge edge) (Resolved Interact [edgeId edge, edgeId e]) edge g1
    !g3 = markEdgeResolved (getGroupFromEdge e) (Resolved Interact [edgeId edge, edgeId e]) e g2
    in return g3
applyInteractResult _ (_, NotApplicable) graph = return graph
applyInteractResult edge (e, Applied ncs) graph = do
    let c1 = getConstraintFromEdge edge
    let c2 = getConstraintFromEdge e

    let gMe1 = if c1 `elem` ncs then graph else markEdgeResolved (maxGroup e edge) (Resolved Interact [edgeId edge, edgeId e]) edge graph
    let gMe2 = if c2 `elem` ncs then gMe1 else markEdgeResolved (maxGroup edge e) (Resolved Interact [edgeId edge, edgeId e]) e gMe1
    ruleIsApplied Interact [getConstraintFromEdge edge, getConstraintFromEdge e] (show (Applied ncs))
    ncs' <- mapM (\nc -> convertConstraint [edgeId edge, edgeId e] False (isEdgeGiven edge && isEdgeGiven e) (maxGroup edge e) (maxPriority nc edge e) nc) (ncs \\ [c1, c2])
    let g' = insertGraphs gMe2 ncs'
    return $ markInfluencesEdges (concatMap (map edgeId . getUnresolvedConstraintEdges') ncs') [edgeId edge, edgeId e] g' 

applySimplifyRule :: (HasTypeGraph m axiom touchable types constraint ci) => Groups -> Priority -> EdgeId -> TGGraph touchable types constraint ci -> m(TGGraph touchable types constraint ci) 
applySimplifyRule groups' curPrior edgeIndex graph = do
    let edge = getEdgeFromId graph edgeIndex
    if isEdgeGiven edge || not (isUnresolvedConstraintEdge groups' edge) || getPriorityFromEdge edge /= curPrior || not (sameGroups (getGroupFromEdge edge) groups') then -- && priority (edgeCategory edge) == curPrior then
        return graph
    else do
        let doneEdges = concatMap getEdgesFromMultirule $ filter (MultiRule Simplify [] ==) (rulesTried $ edgeCategory edge)
        candidateEdges <- getSimplificationCandidates doneEdges edge graph
        foldM (\g ei -> do
            setGraph g
            let e = getEdgeFromId g ei
            let edge' = getEdgeFromId g edgeIndex
            if isUnresolvedConstraintEdge groups' edge' && edgeId e /= edgeId edge' && getGroupFromEdge e `isSuffixOf` getGroupFromEdge edge' then do
                result <- simplify (getConstraintFromEdge e) (getConstraintFromEdge edge') 
                applySimplifyResult e (edge', result) g
            else
                return g

            ) graph (nub $ map edgeId $ filter (\e -> isConstraintEdge e && (getPriorityFromEdge e < curPrior)) candidateEdges)

applySimplifyResult :: (HasTypeGraph m axiom touchable types constraint ci) => TGEdge constraint -> (TGEdge constraint, RuleResult [constraint]) -> TGGraph touchable types constraint ci -> m (TGGraph touchable types constraint ci)
applySimplifyResult eGiven (e, Error label) graph = let
    g1 = makeIncorrect label eGiven graph
    g2 = markEdgeResolved (getGroupFromEdge eGiven) (Resolved Simplify [edgeId eGiven, edgeId e]) eGiven g1
    in return g2
applySimplifyResult _ (_, NotApplicable) graph = return graph
applySimplifyResult eGiven (e, Applied ncs) graph = do
    let gMe1 = markEdgeResolved (getGroupFromEdge e) (Resolved Simplify [edgeId eGiven, edgeId e]) e graph
    ruleIsApplied Simplify [getConstraintFromEdge eGiven, getConstraintFromEdge e] (show $ Applied ncs)
    ncs' <- mapM (convertConstraint [edgeId eGiven, edgeId e] False False (getGroupFromEdge e) (getPriorityFromEdge e)) ncs
    let g' = insertGraphs gMe1 ncs'
    return $ markInfluencesEdges (concatMap (map edgeId . getUnresolvedConstraintEdges') ncs') [edgeId eGiven, edgeId e] g' 

applyTopLevelReactRule :: (HasTypeGraph m axiom touchable types constraint ci) => Groups -> EdgeId -> TGGraph touchable types constraint ci -> m(TGGraph touchable types constraint ci) 
applyTopLevelReactRule groups' edgeIndex graph = do
    let edge = getEdgeFromId graph edgeIndex
    let graph' = markEdgeTried (SingleRule TopLevelReact) edge graph
    if isUnresolvedConstraintEdge groups' edge then do 
        result <- topLevelReact (isEdgeGiven edge) (getConstraintFromEdge edge)
        applyReactResult edge result graph'
    else
        return graph'

applyReactResult :: (HasTypeGraph m axiom touchable types constraint ci) => TGEdge constraint -> RuleResult ([touchable], [constraint]) -> TGGraph touchable types constraint ci -> m (TGGraph touchable types constraint ci)
applyReactResult edge (Error label) graph = return (makeIncorrect label edge graph)
applyReactResult _ NotApplicable graph = return graph
applyReactResult edge (Applied (vars, ncs)) graph = do
    let g' = markEdgeResolved (getGroupFromEdge edge) (Resolved TopLevelReact [edgeId edge]) edge graph
    ruleIsApplied TopLevelReact [getConstraintFromEdge edge] (show (Applied (vars, ncs)))
    ncs' <- mapM (convertConstraint [edgeId edge] False (isEdgeGiven edge) (getGroupFromEdge edge) (priority (edgeCategory edge))) ncs
    return 
        $ markInfluencesEdges (concatMap (map edgeId . getUnresolvedConstraintEdges' ) ncs') [edgeId edge] 
        $ markTouchables (map (\v -> (v, priority $ edgeCategory edge)) vars) 
        $ insertGraphs g' ncs'

resolvePriorityConstraints :: (Show touchable, Show types, Monad m, Eq constraint, IsEquality types constraint touchable, Show constraint) => Bool -> Groups -> Priority -> TGGraph touchable types constraint ci -> m (TGGraph touchable types constraint ci)
resolvePriorityConstraints ignoreTouchable group' p g 
    | odd p, p > 1 = do
        let (unresolvedUnify, unresolvedOther) 
                = partition (isEquality . getConstraintFromEdge) 
                $ filter (\e -> priority (edgeCategory e) == p && getGroupFromEdge e == group' && isUnresolvedConstraintEdge group' e) 
                $ getUnresolvedConstraintEdgesByPriority p g
        let (touchableUnresolved, incorrectEdges) = partition (\e -> ignoreTouchable || isConstraintTouchable p g e) unresolvedUnify
        let gResolved = foldr (\e -> markEdgeResolved (getGroupFromEdge e) (Resolved Substitution []) e) g touchableUnresolved
        let gErrors = foldr 
                (\e g' -> makeIncorrect labelResidual e g') 
                gResolved 
                (incorrectEdges ++ unresolvedOther)
        return gErrors
    | otherwise = return g    

