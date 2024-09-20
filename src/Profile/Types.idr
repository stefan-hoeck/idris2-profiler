module Profile.Types

import Debug.Trace
import public Data.DPair
import public Data.Nat
import public Data.Vect
import public System.Clock

%default total

--------------------------------------------------------------------------------
--          Format
--------------------------------------------------------------------------------

public export
data Format = Table | Details

--------------------------------------------------------------------------------
--          Pos
--------------------------------------------------------------------------------

||| A strictly positive natural number.
public export
record Pos where
  constructor MkPos
  val   : Nat
  {auto 0 prf : IsSucc val}

export
Eq Pos where (==) = (==) `on` val

export
Ord Pos where compare = compare `on` val

public export
fromInteger : (n : Integer) -> (0 prf : IsSucc (cast n)) => Pos
fromInteger n = MkPos (cast n)

--------------------------------------------------------------------------------
--          Benchmarkable
--------------------------------------------------------------------------------

||| A benchmarkable computation, which can fail with error `err`.
public export
record Benchmarkable (err : Type) where
  constructor MkBenchmarkable
  {0 environment : Type}

  {0 result      : Type}

  ||| Allocates an environment for running the benchmark
  ||| the given number of times.
  allocEnv      : Pos -> IO environment

  ||| Cleanup the environment after running the benchmark
  ||| the given number of times.
  cleanEnv      : Pos -> environment -> IO ()

  ||| Run a benchmurk in the given environment for
  ||| the given number of times.
  runRepeatedly : environment -> Pos -> IO (Either err result)

  ||| True, if this is a pure computation and we are only interested
  ||| in the time spent on the CPU.
  cpuOnly       : Bool

repeatedly_ : Nat -> PrimIO (Either err ()) -> PrimIO (Either err ())
repeatedly_ 0     _ w = MkIORes (Right ()) w
repeatedly_ (S k) f w =
  let MkIORes (Right _) w2 := f w | res => res
   in repeatedly_ k f w2

||| Tail-recursively runs an IO action the given number
||| of times or until it returns `False`, signaling a
||| failure.
export
repeatedly : Pos -> IO (Either err ()) -> IO (Either err ())
repeatedly (MkPos n) io = fromPrim $ repeatedly_ n (toPrim io)

export
singleIO : IO () -> Benchmarkable Void
singleIO io =
  MkBenchmarkable
    { allocEnv = \_ => pure ()
    , cleanEnv = \_,_ => pure ()
    , runRepeatedly = \(),n => repeatedly n (map Right io)
    , cpuOnly  = False
    }

repeatedlyPure_ : Nat -> a -> (() -> Either err a) -> Either err a
repeatedlyPure_ 0     v _ = Right v
repeatedlyPure_ (S k) v f = case f () of
  Right v2 => repeatedlyPure_ k v2 f
  Left err => Left err

export
repeatedlyPure : Pos -> (() -> Either err a) -> Either err a
repeatedlyPure (MkPos $ S n) f = case f () of
  Left err => Left err
  Right v  => repeatedlyPure_ n v f

export
singlePure : (() -> Either err a) -> Benchmarkable err
singlePure f =
  MkBenchmarkable
    { allocEnv = \_ => pure ()
    , cleanEnv = \_,_ => pure ()
    , runRepeatedly = \(),n => map (`repeatedlyPure` f) (pure n)
    , cpuOnly  = True
    }

export
basic : (a -> b) -> a -> Benchmarkable Void
basic f va = singlePure (\_ => let v = f va in Right v)

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

--------------------------------------------------------------------------------
--          Scalars
--------------------------------------------------------------------------------

public export
record SUnit where
  constructor U
  atto : Integer
  run  : Integer

namespace SUnit
  public export
  times : SUnit -> SUnit -> SUnit
  -- this makes sure that multiplication by a unit-less scalar
  -- reduces during unification
  times (U 0 0)   u         = u
  times (U a1 r1) (U a2 r2) = U (a1 + a2) (r1 + r2)

  public export
  div : SUnit -> SUnit -> SUnit
  -- this makes sure that division by a unit-less scalar
  -- reduces during unification
  div u         (U 0 0)   = u
  div (U a1 r1) (U a2 r2) = U (a1 - a2) (r1 - r2)

public export
record Scalar (u : SUnit) where
  constructor MkScalar
  val : Integer

public export
Eq (Scalar u) where (==) = (==) `on` val

public export
Ord (Scalar u) where compare = compare `on` val

namespace Scalar
  public export
  fromInteger : Integer -> Scalar u
  fromInteger = MkScalar

public export
0 AttoSeconds : Type
AttoSeconds = Scalar (U 1 0)

public export
0 AttoSecondsPerRun : Type
AttoSecondsPerRun = Scalar (U 1 (-1))

public export
0 Runs : Type
Runs = Scalar (U 0 1)

public export
plus : Scalar u -> Scalar u -> Scalar u
plus x y = MkScalar $ x.val + y.val

public export
minus : Scalar u -> Scalar u -> Scalar u
minus x y = MkScalar $ x.val - y.val

public export
scalarSum : Foldable t => t (Scalar u) -> Scalar u
scalarSum = foldl plus 0

public export
mult : Scalar u1 -> Scalar u2 -> Scalar (times u1 u2)
mult x y = MkScalar $ x.val * y.val

public export
div : Scalar u1 -> Scalar u2 -> Scalar (div u1 u2)
div x y = MkScalar $ x.val `div` y.val

public export
posLength : Vect (S n) a -> Scalar (U 0 0)
posLength = MkScalar . cast . length

public export
fromFemtoSeconds : Integer -> AttoSeconds
fromFemtoSeconds = fromInteger . (* 1000)

public export
fromPicoSeconds : Integer -> AttoSeconds
fromPicoSeconds = fromFemtoSeconds . (* 1000)

public export
fromNanoSeconds : Integer -> AttoSeconds
fromNanoSeconds = fromPicoSeconds . (* 1000)

public export
fromMicroSeconds : Integer -> AttoSeconds
fromMicroSeconds = fromNanoSeconds . (* 1000)

public export
fromMilliSeconds : Integer -> AttoSeconds
fromMilliSeconds = fromMicroSeconds . (* 1000)

public export
fromSeconds : Integer -> AttoSeconds
fromSeconds = fromMilliSeconds . (* 1000)

public export
fromClock : Clock Duration -> AttoSeconds
fromClock c =
  plus
    (fromNanoSeconds $ nanoseconds c)
    (fromSeconds $ seconds c)

export
timeDelta : Clock t -> Clock t -> AttoSeconds
timeDelta c1 c2 = fromClock $ timeDifference (max c1 c2) (min c1 c2)

export
toFloat : Scalar u -> Double
toFloat = cast . val

--------------------------------------------------------------------------------
--          Measured
--------------------------------------------------------------------------------

||| A collection of measurements made while benchmarking
public export
record Measured where
  constructor MkMeasured
  ||| Number of iterations
  iterations : Runs

  ||| True, if we are interested only in the CPU time
  cpuOnly    : Bool

  ||| Wall clock time when starting the measurement
  startTime  : Clock Monotonic

  ||| Wall clock time when stopping the measurement
  stopTime   : Clock Monotonic

  ||| Total wall clock time elapsed in atto seconds
  totalTime  : AttoSeconds

  ||| Average wall clock time elapsed per iteration
  avrgTime   : AttoSecondsPerRun

  ||| Total CPU time elapsed
  cpuTime    : AttoSeconds

  ||| Average CPU time elapsed per iteration
  avrgCPU    : AttoSecondsPerRun

export
tot : Measured -> AttoSeconds
tot m = if m.cpuOnly then m.cpuTime else m.totalTime

export
avrg : Measured -> AttoSecondsPerRun
avrg m = if m.cpuOnly then m.avrgCPU else m.avrgTime

--------------------------------------------------------------------------------
--          Result of running a single benchmark
--------------------------------------------------------------------------------

public export
record Result where
  constructor MkResult
  name      : String
  runs      : List Measured
