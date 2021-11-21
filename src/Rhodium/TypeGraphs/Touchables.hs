{-# LANGUAGE MultiParamTypeClasses #-}
-- | A module regarding the touchability of variables
module Rhodium.TypeGraphs.Touchables where

import Control.Monad

import qualified Data.Map as M

import Data.Maybe

import Rhodium.TypeGraphs.Graph

-- | Returns a fresh variable
class Monad m => FreshVariable m a where
    freshVariable :: m a

-- | Go over the entire graph, resetting the touchables based on the given list of touchables
markTouchablesReset1 :: Eq touchable => [(touchable, Priority)] -> TGGraph touchable types constraint ci -> TGGraph touchable types constraint ci
markTouchablesReset1 ts g = g{
    vertices = M.map updateTouchable (vertices g)
    }
    where
        updateTouchable vc@TGVariable{} = vc{isTouchable = lookup (variable vc) ts}
        updateTouchable vc = vc

-- | Go over the entire graph, adding the touchables based on the given list of touchables
markTouchables :: Eq touchable => [(touchable, Priority)] -> TGGraph touchable types constraint ci -> TGGraph touchable types constraint ci
markTouchables ts g = g{
    vertices = M.map updateTouchable (vertices g)
    }
    where
        updateTouchable vc@TGVariable{} = vc{isTouchable = mplus (isTouchable vc) (lookup (variable vc) ts)}
        updateTouchable vc = vc


