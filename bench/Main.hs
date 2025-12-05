module Main where

import Base

import Data.List (sort, intercalate)
import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import System.Timeout (timeout)
import Control.Exception (evaluate)
import Test.Tasty (testGroup)
import Test.Tasty.Bench
import Test.QuickCheck hiding (Success, Failure)

import Language.Expr
import Language.Parser
import Language.Problem
import Language.Prelude
import Tactic.Options
import Tactic.Core
import Tactic.Fold qualified as Tactic
import Synth

import Bench hiding (testSynthesis)
import System.Directory (listDirectory)

type Problems = [Named [Named (Problem, Model)]]

getBenchmark :: IO Problems
getBenchmark = forM models . mapM $ mapM \(Named name model@(Model fun)) -> do
  problem <- loadProblem name

  -- Check if model execution agrees with the input-output examples.
  forM_ problem.examples \(Example inputs output) -> if execute fun inputs == output
    then pure () else do
      let ins = inputs <&> \input -> "(" <> show (pretty input) <> ")"
      putStrLn $ "error when calling: " <> Text.unpack name.getName <> concatMap (' ':) ins
      putStrLn $ "problem says: " <> show (pretty output)
      putStrLn $ "model returns: " <> show (pretty (execute fun inputs))

  return $ Named name (problem, model)

synthCheck :: SynthOptions -> Problem -> Model -> IO (String, Bool)
synthCheck args problem (Model model) = do
  timed <- timeout 1_000_000 . Control.Exception.evaluate $ synthesize args problem
  case timed of
    Nothing -> return (yellow "timeout", False)
    Just (Failure Depleted) -> return ("out of fuel", True)
    Just (Failure Exhausted) -> return (blue "unrealizable", True)
    Just (Success ((_, Unfinished _filling) :| _)) -> return (yellow "realizable", True)
    Just (Success ((_, Finished program) :| _))
      | testProblem program problem -> do
        result <- quickCheckWithResult stdArgs { chatty = False }
          . withMaxSize 25 $ comparison model (interpret program)
        return if isSuccess result
          then (green "success", True)
          else (red "overfit", True)
      | otherwise -> return (red_bg "inconsistent result", True)
    where
      red    text = "\ESC[31m" ++ text ++ "\ESC[0m"
      green  text = "\ESC[32m" ++ text ++ "\ESC[0m"
      yellow text = "\ESC[33m" ++ text ++ "\ESC[0m"
      blue   text = "\ESC[34m" ++ text ++ "\ESC[0m"
      red_bg text = "\ESC[41m" ++ text ++ "\ESC[0m"

data BenchOptions
  = NoFeasibility
  | Feasibility { coverage :: Bool, branching :: Bool }

allOptions :: [BenchOptions]
allOptions =
  [ NoFeasibility
  , Feasibility { coverage = False, branching = False }
  , Feasibility { coverage = True , branching = False }
  , Feasibility { coverage = False, branching = True  }
  , Feasibility { coverage = True , branching = True  }
  ]

instance Pretty BenchOptions where
  pretty = \case
    NoFeasibility -> "no feasibility"
    Feasibility { coverage, branching }
      | coverage && branching -> "all settings"
      | coverage -> "coverage"
      | branching -> "branching"
      | otherwise -> "feasibility"

skip :: Benchmarkable
skip = whnf (const ()) ()

-- TODO: ideally this would already filter out the problems that don't fit the pattern given by `--pattern PATTERN`
synthBench :: BenchOptions -> Problems -> IO Benchmark
synthBench options problems = testGroup (show $ pretty options) <$>
  forM problems \group -> do
    groupBenches <- forM group.value \(Named name (problem, model)) -> do
      (message, withinTime) <- synthCheck synArgs problem model
      return $ bench (showName name message) $
        if withinTime then whnf (synthesize synArgs) problem else skip
    return $ testGroup (show $ pretty group.name) groupBenches
  where
    maxLength = maximum $ problems >>= \x -> map (Text.length . (.name.getName)) x.value
    tacticOptions = case options of
      NoFeasibility ->
        def { realizabilityLevel = NoRealizability, checkCoverage = False, conditionalBranch = False }
      Feasibility { coverage, branching } ->
        def { realizabilityLevel = PolyRealizability, checkCoverage = coverage, conditionalBranch = branching }
    synArgs = def { tacticOptions }
    showName :: Name -> String -> String
    showName name message = Text.unpack name.getName <> padding <> "(" <> message <> ")"
      where padding = Base.replicate (maxLength + 3 - Text.length name.getName) ' '

foldBench :: Problems -> IO Benchmark
foldBench problems = testGroup "fold detection" <$>
  forM problems \group -> do
    groupBenches <- forM group.value \(Named name (problem, _)) -> do
      let message = intercalate ", " $ synthesizeAll synArgs problem & mapMaybe \case
            (_, Left NotApplicable{}) -> Nothing
            (_, Left Unrealizable{}) -> Just $ red "failure"
            (_, Left TraceIncomplete{}) -> Just $ red_bg "missing trace"
            (_, Left PropagationError{}) -> Just $ red_bg "propagation error"
            (_, Right{}) -> Just $ green "success"
      return $ bench (showName name message) $ nf (map (fmap isRight) <$> synthesizeAll synArgs) problem
    return $ testGroup (Text.unpack group.name.getName) groupBenches
  where
    maxLength = maximum $ problems >>= \x -> map (Text.length . (.name.getName)) x.value
    -- NOTE: these are reported in opposite order. Hence "ys" before "xs".
    synArgs = def { tactic = Tactic.fold "ys" <|> Tactic.fold "xs" <|> Tactic.fold "t" }
    showName :: Name -> String -> String
    showName name message = Text.unpack name.getName <> padding <> "(" <> message <> ")"
      where padding = Base.replicate (maxLength + 3 - Text.length name.getName) ' '
    red    text = "\ESC[31m" ++ text ++ "\ESC[0m"
    green  text = "\ESC[32m" ++ text ++ "\ESC[0m"
    red_bg text = "\ESC[41m" ++ text ++ "\ESC[0m"

main :: IO ()
main = do
  problems <- getBenchmark

  foldBenches <- foldBench problems
  synthBenches <- forM allOptions \options -> synthBench options problems

  defaultMain
    [ foldBenches
    , testGroup "synthesis" synthBenches
    ]

load :: Name -> IO Problem
load name = do
  content <- Text.readFile $ "data/bench/" <> Text.unpack name.getName
  case lexParse (parser @(Named Problem)) content of
    Nothing -> error $ "Failed to parse " <> show (pretty name)
    Just problem -> return problem.value

foldCheck :: Named Problem -> Benchmark
foldCheck (Named name problem) = bench (Text.unpack name.getName) $ whnf (isFold "xs") problem

isFold :: Name -> Problem -> Bool
isFold var problem = case runTactic def datatypes problem (Tactic.fold var) of
  Left _ -> False
  Right _ -> True

runBenchmark :: FilePath -> IO ()
runBenchmark dir = do
  files <- sort <$> listDirectory dir
  problems <- forM files \name -> do
    content <- Text.readFile $ dir <> name
    case lexParse parser content of
      Nothing -> error $ "Failed to parse " <> show (pretty name)
      Just problem -> return problem

  let maxLength = maximum $ problems <&> Text.length . (.name.getName)

  forM_ problems \(Named name problem) -> do
    let len = Text.length name.getName
    let str = if isFold "xs" problem then "\ESC[32mTrue\ESC[0m" else "\ESC[31mFalse\ESC[0m"
    let padding = Base.replicate (maxLength + 3 - len) ' '
    putStrLn $ show (pretty name) <> ":" <> padding <> str

  defaultMain $ map foldCheck problems

