module GraphSpec where

import Test.Hspec

import TestGraph (TestGraph, Type (..), Constraint (..), runTypeGraphM)

import qualified Data.Map.Strict as M

import Rhodium.TypeGraphs.Graph (TGVertexCategory (..), vertices, emptyTGGraph)
import Rhodium.Core (constructGraph)


emptyTestGraph :: TestGraph
emptyTestGraph = emptyTGGraph

spec :: SpecWith ()
spec =
  describe "Graph" $ do
    it "empty graph should be equal" $ do
      emptyTGGraph `shouldBe` emptyTestGraph
    it "should create an empty graph" $ do
      let given = []
          wanted = []
          touchables = []
      let graph = runTypeGraphM $ constructGraph given wanted touchables
      graph `shouldBe` emptyTestGraph
    it "should create a simple graph" $ do
      let c = ConstraintUnify (TypeConstructor "a") (TypeConstructor "b")
          given = []
          wanted = [c]
          touchables = []
      let graph = runTypeGraphM $ constructGraph given wanted touchables
      vertices graph `shouldBe` M.fromList [ (0, TGConstant "a"), (1, TGConstant "b")]
