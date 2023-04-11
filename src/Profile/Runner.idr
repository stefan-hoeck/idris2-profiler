module Profile.Runner

import Data.Refined.Integer
import Data.String
import Text.Printf
import Profile.Statistics
import Profile.Types

%default total

unitFor : Integer -> String
unitFor 0 = "fs"
unitFor 1 = "ps"
unitFor 2 = "ns"
unitFor 3 = "μs"
unitFor 4 = "ms"
unitFor 5 = " s"
unitFor _ = "s"

nonSec : (sig,exp : Integer) -> String -> String
nonSec sig exp s =
  let (factor,pad) = case exp `mod` 3 of
                       0 => (1000, S 2)
                       1 => (100, S 1)
                       _ => (10, S Z)
      pre  = show $ sig `div` factor
      post = padLeft pad '0' . show $ sig `mod` factor
   in "\{pre}.\{post} \{s}"

printPos : Integer -> String
printPos n = case lte 1000 n of
  Nothing0 => padLeft 8 ' ' "\{show n} as"
  Just0 x  =>
    let (n',exp) = significant n 4 @{weak [0,1000,n]}
        exp'     = cast {to = Integer} exp
     in case unitFor (exp' `div` 3) of
          "s" => case exp `minus` 18 of
            0 => "\{show n'} s"
            e => "\{show n'}e\{show e} s"
          u   => nonSec n' exp' u

printAtto : AttoSecondsPerRun -> String
printAtto (MkScalar v) = if v < 0 then "-" ++ printPos v else printPos v

-- an exponentially growing series of numbers of repetitions
runs : List Pos
runs = go 600 [< 1] 1 1.0
  where go : Nat -> SnocList Pos -> Pos -> Double -> List Pos
        go 0     sx p x = sx <>> Nil
        go (S k) sx p x =
          let nx       = x * 1.05
              n2@(S _) = cast nx | 0 => go k sx p nx
              p2       = MkPos n2
           in go k (if p2.val > p.val then sx :< p2 else sx) p2 nx

-- runs a benchmark once with the given number of
-- interations
run : Pos -> Benchmarkable err -> IO (Either err Measured)
run p (MkBenchmarkable alloc clean go) = do
  env      <- alloc p
  start    <- clockTime Monotonic
  startCPU <- clockTime Process
  res      <- go env p
  stopCPU  <- clockTime Process
  stop     <- clockTime Monotonic
  clean p env

  let tot  = timeDelta start stop
      runs = the Runs $ MkScalar $ cast p.val
      meas = MkMeasured {
          iterations = runs
        , startTime  = start
        , stopTime   = stop
        , totalTime  = tot
        , avrgTime   = tot `div` runs
        , cpuTime    = timeDelta stopCPU startCPU
        }
  case res of
    Left err => pure (Left err)
    Right v  => pure (Right meas)

-- 30 ms
threshold : AttoSeconds
threshold = fromMilliSeconds 30

-- 300 ms
threshold10 : AttoSeconds
threshold10 = fromMilliSeconds 300

||| Run a benchmark with an increasing number of
||| iterations until at least the given time limit
||| has passed.
export
runBenchmark : (timeLimit : AttoSeconds)
             -> Benchmarkable err
             -> IO (Either err $ List Measured)
runBenchmark timeLimit b = do
  startTime <- clockTime Monotonic
  fromPrim $ go Lin runs startTime 0 0
  where go :  SnocList Measured
           -> List Pos
           -> (startTime     : Clock Monotonic)
           -> (overThreshold : AttoSeconds)
           -> (nruns         : Nat)
           -> PrimIO (Either err $ List Measured)
        go sr []        st ot nr w = MkIORes (Right $ sr <>> Nil) w
        go sr (p :: ps) st ot nr w =
          let MkIORes (Right r) w2 = toPrim (run p b) w
                | MkIORes (Left err) w2 => MkIORes (Left err) w2
              diffThreshold = max 0 $ r.totalTime `minus` threshold
              overThreshold = ot `plus` diffThreshold
              tot           = fromClock $ timeDifference r.stopTime st
              done          =
                tot           >= timeLimit   &&
                overThreshold >= threshold10 &&
                nr            >= 4

           in if done then MkIORes (Right (sr <>> [r])) w2
              else go (sr :< r) ps st overThreshold (S nr) w2

detailStats : Nat -> String -> Stats -> String
detailStats k name stats = """
  # \{show k}: \{name}
    time per run : \{printAtto stats.slope}
    mean         : \{printAtto stats.mean}
    r2           : \{show stats.r2}


  """

tableStats : Nat -> String -> Stats -> String
tableStats k name stats =
  let nm   := padRight 50 ' ' name
      tpr  := padLeft 10 ' ' $ printAtto stats.slope
      mean := padLeft 10 ' ' $ printAtto stats.mean
      r2   := pack $ take 5 $ unpack $ show stats.r2
   in "\{nm} \{tpr} \{mean} \{r2}"

showStats : Format -> Nat -> String -> Stats -> String
showStats Table   = tableStats
showStats Details = detailStats

runAndPrint :  Format
            -> Nat
            -> String
            -> Benchmarkable err
            -> IO (Either err ())
runAndPrint format k name b = do
  Right (h :: t) <- runBenchmark (fromSeconds 1) b
    | Right [] => pure (Right ())
    | Left err => pure (Left err)

  putStrLn (showStats format k name $ regr (h :: fromList t))
  pure (Right ())

for :  (String -> Bool)
    -> Benchmark err
    -> (Nat -> String -> Benchmarkable err -> IO (Either err ()))
    -> IO (Either err ())
for select b f = ignore <$> fromPrim (go 1 "" b)
  where many : Nat -> String -> List (Benchmark err) -> PrimIO (Either err Nat)

        go : Nat -> String -> Benchmark err -> PrimIO (Either err Nat)
        go k s (Single name bench) w =
          let s' := addPrefix s name
           in if select s'
                then let MkIORes (Right _) w2 = toPrim (f k s' bench) w
                           | MkIORes (Left err) w2 => MkIORes (Left err) w2
                      in MkIORes (Right $ S k) w2
                else MkIORes (Right k) w
        go k s (Group name benchs) w = many k (addPrefix s name) benchs w

        many k s [] w        = MkIORes (Right k) w
        many k s (b :: bs) w =
          let MkIORes (Right k2) w2 = go k s b w
                | MkIORes (Left err) w2 => MkIORes (Left err) w2
           in many k2 s bs w2

export
runDefault :  (String -> Bool)
           -> Format
           -> (err -> String)
           -> Benchmark err
           -> IO ()
runDefault select format showErr b = do
  Left err <- for select b (runAndPrint format)
    | Right () => pure ()
  putStrLn (showErr err)
