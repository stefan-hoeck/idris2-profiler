module Profile.Runner

import Profile.Types

%default total

-- an exponentially growing series of numbers of repetitions
runs : List Pos
runs = go 600 [< 1] 1 1.0
  where go : Nat -> SnocList Pos -> Pos -> Double -> List Pos
        go 0     sx p x = sx <>> Nil
        go (S k) sx p x =
          let nx       = x * 1.05
              n2@(S _) = cast nx | 0 => go k sx p nx
              p2       = MkPos n2 %search
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

  let meas = MkMeasured {
          iterations = p
        , startTime  = start
        , stopTime   = stop
        , totalTime  = timeDifference start stop
        , cpuTime    = timeDifference startCPU stopCPU
        }
  case res of
    Left err => pure (Left err)
    Right () => pure (Right meas)

-- zero duration
zero : Clock Duration
zero = makeDuration 0 0

-- 30 ms
threshold : Clock Duration
threshold = makeDuration 0 30_000_000

-- 300 ms
threshold10 : Clock Duration
threshold10 = makeDuration 0 300_000_000

||| Run a benchmark with an increasing number of
||| iterations until at least the given time limit
||| has passed.
export
runBenchmark : (timeLimit : Clock Duration)
             -> Benchmarkable err
             -> IO (Either err $ List Measured)
runBenchmark timeLimit b = do
  startTime <- clockTime Monotonic
  fromPrim $ go Lin runs startTime zero 0
  where go :  SnocList Measured
           -> List Pos
           -> (startTime     : Clock Monotonic)
           -> (overThreshold : Clock Duration) 
           -> (nruns         : Nat)
           -> PrimIO (Either err $ List Measured)
        go sr []        st ot nr w = MkIORes (Right $ sr <>> Nil) w
        go sr (p :: ps) st ot nr w =
          let MkIORes (Right r) w2 = toPrim (run p b) w
                | MkIORes (Left err) w2 => MkIORes (Left err) w2
              diffThreshold = max zero $ timeDifference r.totalTime threshold
              overThreshold = addDuration ot diffThreshold
              tot           = timeDifference r.stopTime st
              done          = tot           >= timeLimit   &&
                              overThreshold >= threshold10 &&
                              nr            >= 4

           in if done then MkIORes (Right (sr <>> [r])) w2
              else go (sr :< r) ps st overThreshold (S nr) w2

for :  (String -> Bool)
    -> Benchmark err
    -> (Nat -> String -> Benchmarkable err -> IO (Either err ()))
    -> IO (Either err ())
for select b f = ignore <$> fromPrim (go 1 "" b)
  where many : Nat -> String -> List (Benchmark err) -> PrimIO (Either err Nat)

        go : Nat -> String -> Benchmark err -> PrimIO (Either err Nat)
        go k s (Single name bench) w =
          if select s
             then let MkIORes (Right _) w2 = toPrim (f k s bench) w
                        | MkIORes (Left err) w2 => MkIORes (Left err) w2
                   in MkIORes (Right $ S k) w2
             else MkIORes (Right k) w
        go k s (Group name benchs) w = many k (addPrefix s name) benchs w

        many k s [] w        = MkIORes (Right k) w
        many k s (b :: bs) w =
          let MkIORes (Right k2) w2 = go k s b w
                | MkIORes (Left err) w2 => MkIORes (Left err) w2
           in many k2 s bs w2
