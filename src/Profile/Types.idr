module Profile.Types

import public Data.Nat
import public System.Clock

%default total

--------------------------------------------------------------------------------
--          Pos
--------------------------------------------------------------------------------

||| A strictly positive natural number.
public export
record Pos where
  constructor MkPos
  val   : Nat
  0 prf : IsSucc val

export
Eq Pos where (==) = (==) `on` val

export
Ord Pos where compare = compare `on` val

public export
fromInteger : (n : Integer) -> (0 prf : IsSucc (cast n)) => Pos
fromInteger n = MkPos (cast n) prf

--------------------------------------------------------------------------------
--          Benchmarkable
--------------------------------------------------------------------------------

||| A benchmarkable computation, which can fail with error `err`.
public export
record Benchmarkable (err : Type) where
  constructor MkBenchmarkable
  {0 env        : Type}

  ||| Allocates an environment for running the benchmark
  ||| the given number of times.
  allocEnv      : Pos -> IO env

  ||| Cleanup the environment after running the benchmark
  ||| the given number of times.
  cleanEnv      : Pos -> env -> IO ()

  ||| Run a benchmurk in the given environment for
  ||| the given number of times.
  runRepeatedly : env -> Pos -> IO (Either err ())

repeatedly_ : Nat -> PrimIO (Either err ()) -> PrimIO (Either err ())
repeatedly_ 0     _ w = MkIORes (Right ()) w
repeatedly_ (S k) f w =
  let MkIORes (Right _) w2 = f w | res => res
   in repeatedly_ k f w2

||| Tail-recursively runs an IO action the given number
||| of times or until it returns `False`, signaling a
||| failure.
export
repeatedly : Pos -> IO (Either err ()) -> IO (Either err ())
repeatedly (MkPos n _) io = fromPrim $ repeatedly_ n (toPrim io)

export
singleIO : IO () -> Benchmarkable Void
singleIO io = MkBenchmarkable {
    allocEnv = \_ => pure ()
  , cleanEnv = \_,_ => pure ()
  , runRepeatedly = \(),n => repeatedly n (map Right io)
  }

repeatedlyPure_ : Nat -> (() -> Either err ()) -> Either err ()
repeatedlyPure_ 0     _ = Right ()
repeatedlyPure_ (S k) f = case f () of
  Right _  => repeatedlyPure_ k f
  Left err => Left err

export
repeatedlyPure : Pos -> (() -> Either err ()) -> Either err ()
repeatedlyPure (MkPos n _) f = repeatedlyPure_ n f

export
singlePure : (() -> Either err ()) -> Benchmarkable err
singlePure f = MkBenchmarkable {
    allocEnv = \_ => pure ()
  , cleanEnv = \_,_ => pure ()
  , runRepeatedly = \(),n => map (`repeatedlyPure` f) (pure n)
  }

export
basic : (a -> b) -> a -> Benchmarkable Void
basic f va = singlePure (\_ => ignore $ Right (f va))

--------------------------------------------------------------------------------
--          Measured
--------------------------------------------------------------------------------

||| A collection of measurements made while benchmarking
public export
record Measured where
  constructor MkMeasured
  ||| Number of iterations run
  iterations : Pos

  ||| Wall clock time when starting the measurement
  startTime  : Clock Monotonic

  ||| Wall clock time when stopping the measurement
  stopTime   : Clock Monotonic

  ||| Total wall clock time elapsed
  totalTime  : Clock Duration

  ||| Total CPU time elapsed
  cpuTime    : Clock Duration

--------------------------------------------------------------------------------
--          Result of running a single benchmark
--------------------------------------------------------------------------------

public export
record Result where
  constructor MkResult
  name      : String
  runs      : List Measured

--------------------------------------------------------------------------------
--          Benchmarks
--------------------------------------------------------------------------------

public export
data Benchmark : (err : Type) -> Type where
  Single : (name : String) -> (bench : Benchmarkable err) -> Benchmark err
  Group  : (name : String) -> (benchs : List (Benchmark err)) -> Benchmark err

export
addPrefix : (pre : String) -> (rst : String) -> String
addPrefix ""  rst = rst
addPrefix pre rst = "\{pre}/\{rst}"
