{-
   Fixed-points of contractions using G.Hutton and
   M.Jaskelioff encoding.
-}
module Coinduction.Contractions where
import Data.Maybe (fromMaybe)

type List a = [a]
type Stream a = [a]
type Nat = Integer

hfix :: (List a -> a) -> Stream a
hfix = unfold []
  where unfold history next
          = let new = next history
            in new : unfold (new:history) next

histfibs              :: List Nat -> Nat
histfibs []           =  0
histfibs [x]          =  1
histfibs (x : y : zs) =  y + x

hfibs = hfix histfibs

--------------------------------------------------

data Gen a = (:<) {now :: a, after :: a -> Gen a}
infixr 5 :<
gfix :: Gen a -> Stream a
gfix (x :< xs) = x : gfix (xs x)


genfibs :: Gen Nat
genfibs = 0 :< loop 1
  where loop x y = x :< loop (x + y)
        
gfibs = gfix genfibs
