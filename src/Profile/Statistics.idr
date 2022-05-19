module Profile.Statistics

import Data.Vect
import Profile.Types

%default total

public export
mean : Vect (S n) (Scalar u) -> Scalar u
mean as = scalarSum as `div` posLength as

square : Scalar u -> Scalar (times u u)
square n = mult n n

public export
record Stats where
  constructor MkStats
  slope : AttoSecondsPerRun
  mean  : AttoSecondsPerRun
  r2    : Double

calcR2 : Scalar (U 1 1) -> Scalar (U 2 0) -> Scalar (U 0 2) -> Double
calcR2 it_at at2 it2 = toFloat (square it_at) / toFloat (mult at2 it2)

export
regr : (ms : Vect (S n) Measured) -> Stats
regr ms =
  let iters      = map iterations ms
      attos      = map totalTime ms
      mean_iter  = mean iters
      mean_attos = mean attos
      mean_avrg  = mean (map avrgTime ms)
      ss_iter    =       scalarSum (map square iters)
                 `minus` mult (posLength ms) (square mean_iter)
      ss_atto    =       scalarSum (map square attos)
                 `minus` mult (posLength ms) (square mean_attos)
      ss_it_at   = scalarSum (zipWith mult iters attos)
                 `minus` mult (posLength ms) (mult mean_iter mean_attos)
   in MkStats (ss_it_at `div` ss_iter)
              mean_avrg
              (calcR2 ss_it_at ss_atto ss_iter)
