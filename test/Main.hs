{-# LANGUAGE RequiredTypeArguments #-}

module Main (main) where

import Base

import Data.Text qualified as Text
import Data.Typeable

import Test.QuickCheck (Arbitrary)
import Test.Tasty
import Test.Tasty.QuickCheck (testProperty, forAll, discard, classify, withMaxSize)

import Data.Tree.Binary
import Language.Arbitrary qualified as Arbitrary
import Language.Container.Relation
import Language.Container.Morphism
import Language.Expr
import Language.Problem
import Language.Prelude
import Tactic
import Synth
import Bench

showType :: forall a -> Typeable a => String
showType t = show . typeRep $ Proxy @t

roundTrip :: forall a ->
  (Arbitrary a, FromValue a, ToValue a, Eq a, Show a, Typeable a)
  => TestTree
roundTrip t = testProperty ("@(" <> showType t <> ")")
  \(e :: t) -> fromValue t (toValue t e) == Just e

roundTrips :: TestTree
roundTrips = testGroup "fromExpr . toExpr == Just"
  [ roundTrip (type Int)
  , roundTrip (type Bool)
  , roundTrip (type Ordering)
  , roundTrip (type (Maybe Int))
  , roundTrip (type [Int])
  , roundTrip (type (Either Int Int))
  , roundTrip (type (Tree Int Int))
  ]

normValue :: TestTree
normValue = testProperty "normalize == id @Value"
  \(v :: Value) -> normalize v == v

relationConsistency :: TestTree
relationConsistency = testProperty "checkRelation m (computeRelation m c)" $
  forAll (Arbitrary.valueMap free) \m ->
  forAll (Arbitrary.constraint free) \c ->
    checkRelation m (computeRelation m c)
  where free = ["a", "b", "c"]

ruleConsistency :: TestTree
ruleConsistency = testProperty
  "applyRule (checkExample s (Example i o)) i == Just o" $
  forAll (Arbitrary.sig free) \signature ->
  forAll (Arbitrary.example signature) \example ->
    case checkExample datatypes signature example of
      Left _err -> discard
      Right rule ->
        classify (null $ holes rule.output) "simple" $
        applyRule rule example.inputs == Just example.output
  where free = ["a", "b"]

main :: IO ()
main = do
  defaultMain $ testGroup "all"
    [ roundTrips
    , normValue
    , relationConsistency
    , ruleConsistency
    ]

synthesisSucceeds :: [Named (Problem, Model)] -> TestTree
synthesisSucceeds problems = testGroup "synthesis" $ problems <&> \(Named name (problem, model)) ->
  testProperty (Text.unpack name.getName) . withMaxSize 25 $ testSynthesis args problem model
  where args = def { tacticOptions = def { removeIrrelevant = False } }
