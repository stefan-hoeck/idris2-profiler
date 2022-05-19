module Examples.Main

import Data.List
import Debug.Trace
import Profile

%default total

strs : Nat -> List String
strs n = replicate n "foo"

fibo : Nat -> Nat
fibo 0 = 1
fibo 1 = 1
fibo (S $ S n) = fibo n + fibo (S n)

bench : Benchmark Void
bench = Group "list_ops" [
--   Group "fastConcat" [
--       Single "1"  (basic fibo 1)
--     , Single "5"  (basic fibo 5)
--     , Single "10" (basic fibo 10)
--     , Single "15" (basic fibo 15)
--     , Single "20" (basic fibo 20)
--     ]
   Group "fastConcat" [
       Single "1000" (basic fastConcat $ strs 1000)
     , Single "2000" (basic fastConcat $ strs 2000)
     , Single "3000" (basic fastConcat $ strs 3000)
     , Single "4000" (basic fastConcat $ strs 4000)
     , Single "5000" (basic fastConcat $ strs 5000)
     ]

 , Group "concat" [
       Single "1000" (basic (foldMap id) $ strs 1000)
     , Single "2000" (basic (foldMap id) $ strs 2000)
     , Single "3000" (basic (foldMap id) $ strs 3000)
     , Single "4000" (basic (foldMap id) $ strs 4000)
     , Single "5000" (basic (foldMap id) $ strs 5000)
     ]

 , Group "foldMap id" [
       Single "1000" (basic concat $ strs 1000)
     , Single "2000" (basic concat $ strs 2000)
     , Single "3000" (basic concat $ strs 3000)
     , Single "4000" (basic concat $ strs 4000)
     , Single "5000" (basic concat $ strs 5000)
     ]
  ]

main : IO ()
main = runDefault (const True) show bench
