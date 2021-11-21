{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE TupleSections #-}
-- | A module describing heuristics for type errors
module Rhodium.Blamer.Heuristics where

import Rhodium.Solver.Rules
import Rhodium.Solver.Simplifier

import Rhodium.TypeGraphs.Graph
import Rhodium.TypeGraphs.GraphUtils
import Rhodium.TypeGraphs.GraphProperties

import Rhodium.Blamer.ErrorUtils
import Rhodium.Blamer.Path

import Data.List
import Control.Monad

import qualified Data.Map as M 


-- | A function from a path to a list of heuristics
type Heuristics m axiom touchable types constraint ci = Path m axiom touchable types constraint ci -> [Heuristic m axiom touchable types constraint ci]

-- | A heuristic data type that is either a voting heuristic of a filter heuristics
data Heuristic m axiom touchable types constraint ci
    = Filter String 
            (HasTypeGraph m axiom touchable types constraint ci => [(constraint, EdgeId, ci, GraphModifier m axiom touchable types constraint ci)] -> m [(constraint, EdgeId, ci, GraphModifier m axiom touchable types constraint ci)])
            --(GraphModifier touchable types constraint ci) 
    | Voting [VotingHeuristic m axiom touchable types constraint ci]
    
-- | A voting heuristic that can either be used on a single part of the path or on the entire path at once
data VotingHeuristic m axiom touchable types constraint ci
    = SingleVoting String (HasTypeGraph m axiom touchable types constraint ci => (constraint, EdgeId, ci, GraphModifier m axiom touchable types constraint ci) -> m (Maybe (Int, String, constraint, EdgeId, ci, GraphModifier m axiom touchable types constraint ci))) 
    | MultiVoting String (HasTypeGraph m axiom touchable types constraint ci => [(constraint, EdgeId, ci, GraphModifier m axiom touchable types constraint ci)] -> m (Maybe (Int, String, [constraint], [EdgeId], ci, GraphModifier m axiom touchable types constraint ci))) 
            --(GraphModifier touchable types constraint ci) -- Modify the graph, if it works, sollution is accepted, if not, edge is permanently rejected, working is defined an error that was not previously found for this edge or giving less errors

-- | Returns the name of the voting heuristic
getVotingHeuristicName :: VotingHeuristic m axiom touchable types constraint ci -> String
getVotingHeuristicName (SingleVoting s _) = s
getVotingHeuristicName (MultiVoting s _) = s

-- | Show instance for the heuristic
instance Show (Heuristic m axiom touchable types constraint  ci) where
    show (Filter s _) = "Filter Heuristic: " ++ s
    show (Voting vhs) = "Voting Heuristic: " ++ intercalate ", " (map show vhs)

-- | Show instance for the voting heuristic
instance Show (VotingHeuristic m axiom touchable types constraint ci) where
    show (SingleVoting s _) = "Single vote heuristic: " ++ s
    show (MultiVoting s _) = "Multi vote heuristic: " ++ s
    
-- | Applies the heuristics on the path in the given graph    
applyHeuristics :: HasTypeGraph m axiom touchable types constraint ci 
                        => Heuristics m axiom touchable types constraint ci 
                        -> Path m axiom touchable types constraint ci -- ^Edges that are allowed to be modified, might nog be continious
                        -> TGGraph touchable types constraint ci 
                        -> m (TGGraph touchable types constraint ci, (ci, constraint, (constraint, ErrorLabel), TGEdge constraint))
applyHeuristics heuristics path graph = do    
    (ci, eid, l, gm) <- evalHeuristic (heuristics path) path graph
    let edge = getEdgeFromId graph eid
    logMsg ""
    logMsg " ------------------------------ "
    logMsg ("Path reduced: " ++ show (idsFromPath path) ++ " => " ++ show eid ++ ", " ++ show (getConstraintFromEdge edge))
    (g', ci') <- applyGraphModifier (eid, constraintFromPath path, ci) gm graph
    return (addResolvedError (edge, ci', getConstraintFromEdge edge, snd l) g', (ci', getConstraintFromEdge edge, l, edge))

-- | Applied a given graph modifier on a graph
applyGraphModifier  :: HasTypeGraph m axiom touchable types constraint ci 
                    => (EdgeId, constraint, ci)
                    -> GraphModifier m axiom touchable types constraint ci 
                    -> TGGraph touchable types constraint ci 
                    -> m (TGGraph touchable types constraint ci, ci ) 
applyGraphModifier param gm graph = do
    (g', ci) <- gm param graph
    (, ci) <$> simplifyGraph False g'

-- | Evaluate the heuristics on the path    
evalHeuristic   :: HasTypeGraph m axiom touchable types constraint ci 
                => [Heuristic m axiom touchable types constraint ci ] 
                -> Path m axiom touchable types constraint ci -- ^Edges that are allowed to be modified, might nog be continious
                -> TGGraph touchable types constraint ci 
                -> m (ci, EdgeId, (constraint, ErrorLabel), GraphModifier m axiom touchable types constraint ci)
evalHeuristic [] (Path _ []) _graph = error "All paths removed by heuristics"
evalHeuristic [] (Path cl@(_, c, l) ((_, eid, ci, gm) : re)) _graph = do
    logMsg " ---------- Result of heuristics ----------"
    logMsg ("Blamed edge: " ++ show eid ++ " with label " ++ show l)  
    unless (null re) (logMsg ("Remaining edges that cannot be reduced by heuristics: " ++ show (idsFromPath $ Path cl re)))
    return (ci, eid, (c, l), gm)
evalHeuristic (h:hs) p@(Path label es) graph =
    if null es then error (show "Current heuristic" ++ show h) else
    case h of
        Filter s f -> do
            es' <- f es
            logMsg ("Apply filter: " ++ s ++ " " ++ shrunkAndFinalMsg es es')
            logMsg ("  Removing edges: " ++ show (map (\(_, ei, _, _) -> ei) $ filter (\(_, ei, _, _) -> ei `notElem` idsFromPath (Path label es')) es))
            logMsg ("  Remainging edges: " ++ show (idsFromPath (Path label es')))
            when (null es') (error (s ++ " removed everything!")) 
            evalHeuristic hs (Path label es') (updateConstraintInformation (map (\(_, ei, ci, _) -> (ei, ci)) es') graph)
        Voting vhs -> do
            logMsg ("Apply " ++ show (length vhs) ++ " voting heuristics")
            res <- mapM (evalVoteHeuristic p) vhs
            let successList = [ (getVotingHeuristicName s, x) | (s, xs) <- zip vhs res, x <- xs ]
                (thePrio, listWithBest) = foldr op (minBound, []) successList
                op (selname, (prio, _, cons, eid, info, gm)) best@(i, list) =
                    case compare prio i of
                        LT -> best
                        EQ -> (i, (selname, (cons, eid, info, gm)):list)
                        GT -> (prio, [(selname, (cons, eid, info, gm))])
                heuristicNames = map fst listWithBest
                remainingEdges = map snd listWithBest
            case listWithBest of 
                [] ->   do 
                            logMsg "Unfortunately, none of the heuristics could be applied"
                            when (null es) (error ("voting" ++ " removed everything!")) 
                            evalHeuristic hs p graph
                _  ->   do 
                            when (null remainingEdges) (error ("voting" ++ " removed everything!")) 
                            logMsg ("Apply voting result: " ++ show heuristicNames)
                            logMsg ("Selected with priority "++show thePrio++": "++ show (map (\(_, ei, _, _) -> ei) remainingEdges) ++"\n")
                            evalHeuristic hs (Path label remainingEdges) (updateConstraintInformation (map (\(_, ei, ci, _) -> (ei, ci)) remainingEdges) graph)

-- | Evaluate a voting heuristic, letting all voting heuristics vote on the path        
evalVoteHeuristic   :: HasTypeGraph m axiom touchable types constraint ci 
                    => Path m axiom touchable types constraint ci
                    -> VotingHeuristic m axiom touchable types constraint ci 
                    -> m [(Int, String, constraint, EdgeId, ci, GraphModifier m axiom touchable types constraint ci)]
evalVoteHeuristic (Path _label edges') vh = 
    case vh of
        SingleVoting s f -> let
                op list e@(constraint', eid, ci, _) = do
                    r <- f e
                    case r of
                        Nothing -> return list
                        Just x@(v, s', _, _, _, _) -> do
                            logMsg ("    " ++ s')
                            logMsg ("    Result: " ++ show (v, constraint', eid, ci))
                            return (x : list)
            in do 
                logMsg ('-' : s)
                foldM op [] edges'
        MultiVoting s f -> do
            logMsg ('-' : s)
            es <- f edges'
            case es of
                Nothing -> return []
                Just _ -> error (show s)
 
-- | Displays an additional message in the log, depending on the length of the lists
shrunkAndFinalMsg :: [a] -> [a] -> String
shrunkAndFinalMsg old new =
    let 
        tag :: String -> String
        tag s = "~" ++ s ++ "~"
    in
    if length new < length old then
        if length new == 1 then
            tag "shrunk" ++ " " ++ tag "final"
        else
            tag "shrunk"
    else
        tag "unmodified"



highParticipation :: (HasLogInfo m, HasTypeGraph m axiom touchable types constraint ci) => Double -> Path m axiom touchable types constraint ci -> Heuristic m axiom touchable types constraint ci
highParticipation ratio _path =
    Filter "Participation ratio" selectTheBest
        where
            selectTheBest :: HasTypeGraph m axiom touchable types constraint ci => [(constraint, EdgeId, ci, GraphModifier m axiom touchable types constraint ci)] -> m [(constraint, EdgeId, ci, GraphModifier m axiom touchable types constraint ci)]
            selectTheBest es = do
                graph <- getGraph
                let paths = mergePaths (extendErrorEdges (error "Unneeded graph modifier") getErrorEdges graph ++ 
                            extendErrorEdges (error "Unneeded graph modifier") (getResidualEdges graph) graph)
                logMsg (show paths)
                let (nrOfPaths, fm)   = participationMap paths 
                    participationList = M.filterWithKey p fm
                    p cnr _    = cnr `elem` activeCNrs
                    activeCNrs = [ cnr | (_, cnr, _, _) <- es ]
                    maxInList  = maximum (M.elems participationList)
                    limit     -- test if one edge can solve it completely
                        | maxInList == nrOfPaths = maxInList 
                        | otherwise              = round (fromIntegral maxInList * ratio) `max` 1
                    goodCNrs   = M.keys (M.filter (>= limit) participationList)
                    bestEdges  = filter (\(_, cnr,_, _) -> cnr `elem` goodCNrs) es
           
                    -- prints a nice report
                    mymsg  = unlines ("" : title : replicate 100 '-' : map f es)
                    title  = "cnr  constraint                                                                ratio   info"
                    f (cons, cnr, info, _gm) = 
                        take 5  (show cnr++(if cnr `elem` goodCNrs then "*" else "")++repeat ' ') ++
                        take 74 (show cons++repeat ' ') ++
                        take 8  (show (M.findWithDefault 0 cnr fm * 100 `div` nrOfPaths)++"%"++repeat ' ') ++
                        "{"++show info++"}"
                logMsg mymsg
                return $ if null bestEdges then es else bestEdges
                        