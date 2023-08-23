module Text.Printf

import Data.DPair
import Data.Refined.Integer

%default total

pow10 : Nat -> Integer
pow10 0     = 1
pow10 (S k) = 10 * pow10 k

||| Extract the `n` most significant digits from a
||| non-negative integer plus the exponent representing
||| the remaining digits.
|||
||| For example, for `v = 123456789` and `n = 3`, this
||| would return `(123,5)`, so that `v ~ 123 * 10^5`.
export
significant :
     (v : Integer)
  -> (n : Nat)
  -> {auto 0 _ : 0 <= v}
  -> (Integer,Nat)
significant v n = go v 0 (pow10 n)
  -- This just keeps dividing the remainder by 10
  -- until it drops below the number of desired digits.
  -- The complexity comes from the totality proof, which
  -- is definitely overkill here but still oddly satisfying.
  where
    go :
         (rem : Integer)
      -> (exp : Nat)
      -> (max : Integer)
      -> (Integer,Nat)
    go rem exp max = case lt rem max of
      Nothing0 => go (assert_smaller rem (rem `div` 10)) (S exp) max
      Just0 x  => (rem,exp)
