module Text.Printf

import Data.DPair
import Data.Prim.Integer.Extra

%default total

pow10 : Nat -> Subset Integer (> 0)
pow10 0     = Element 1 %search
pow10 (S k) =
  let Element v prf = pow10 k
   in Element (10 * v) (multPosPosGT0 10 v %search prf)

||| Extract the `n` most significant digits from a
||| non-negative integer plus the exponent representing
||| the remaining digits.
|||
||| For example, for `v = 123456789` and `n = 3`, this
||| would return `(123,5)`, so that `v ~ 123 * 10^5`.
export
significant : (v : Integer) -> (n : Nat) -> (0 _ : v >= 0) => (Integer,Nat)
significant v n = go v 0 (pow10 n) (accessLT v)
  -- This just keeps dividing the remainder by 10
  -- until it drops below the number of desired digits.
  -- The complexity comes from the totality proof, which
  -- is definitely overkill here but still oddly satisfying.
  where go :  (rem : Integer)
           -> (exp : Nat)
           -> (max : Subset Integer (> 0))
           -> (0 acc : Accessible (BoundedLT 0) rem)
           -> (Integer,Nat)
        go rem exp max (Access rec) = case testLT {lt = (<)} rem max.fst of
          Left0  _ => (rem,exp)
          Right0 p =>
            let 0 remPos = trans_LT_LTE max.snd p
                0 pdiv   = divGreaterOneLT {d = 10} remPos %search
                0 pdiv2  = divNonNeg {d = 10} (Left remPos) %search
             in go (rem `div` 10) (S exp) max (rec _ %search)
