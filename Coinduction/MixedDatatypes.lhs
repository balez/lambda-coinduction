Causal functions over different coinductive types.

In Causal.lhs, functions over a single coinductive types were
considered, for instance [zip : Str a -> Str a -> Str a].

However, a generalisation is possible, where a function can
have inputs in different coinductive types and output in a different
coinductive type.

> {-# LANGUAGE
>      GADTs
> , MultiParamTypeClasses
> , TypeFamilies
> , FlexibleContexts
> , DeriveFunctor
> , Rank2Types
> , FunctionalDependencies
> , TypeOperators
> #-}

> module Coinduction.MixedDatatypes where

Gadts are indexed types, thus we use a version of the causal
library that supports indexed types.

> import qualified Coinduction.Causal as C
> import Coinduction.CausalParam hiding (Cons, Apply, app)
> import Auxiliary.Composition (res2)
> import Prelude hiding (take)

  An example of a causal function over different coinductive
  types is the flatten function over infinite binary trees that
  computes a stream of all the labels of the tree.

> data Tree a = Fork a (Tree a) (Tree a)
> data Stream a = Cons a (Stream a)
>
> flatten_ (Fork x l r) = Cons x (merge_ (flatten_ l) (flatten_ r))

  Merge takes two streams and merge their elements by
  alternating between the two streams:

  merge (x1:x2:x3:...) (y1:y2:y3:...) = x1:y1:x2:y2:x3:y3:...

  it is a causal function

> merge_ (Cons x xs) ys = Cons x (merge_ ys xs)

  Let's define a GADT as a family capturing the union of Tree
  and Stream. First we define two type labels identifying the
  types as indices of the Gadt.

> data TREE
> data STREAM

  Now we define the base functors of Tree and Stream. index
  functors map an indexed type to an indexed type, thus have
  kind: (* -> *) -> * -> *. Therefore they take two parameters,
  one of kind (* -> *) and the other of kind '*'.

> data G a x l where
>   Fork_ :: a -> x TREE -> x TREE -> G a x TREE
>   Cons_ :: a -> x STREAM -> G a x STREAM

> instance PFunctor (G a) where
>   pmap g (Fork_ x l r) = Fork_ x (g l) (g r)
>   pmap g (Cons_ x xs) = Cons_ x (g xs)

Implementing Merge as a causal function. We define a term
functor that only works on streams.

> data Merge a x l where
>   Merge :: x STREAM -> x STREAM -> Merge a x STREAM
> merge = res2 inTerm Merge

> instance PFunctor (Merge a) where
>   pmap g (Merge l r) = Merge (g l) (g r)

> instance IsCausal (Merge a) (G a) where
>   step' (Merge (_ :@ Cons_ x xs) (ys :@ _)) =
>             Cons_ x (merge ys xs)

Implementing Flatten as a causal function. Notice that the
constructor has an argument of type TREE but constructs a
value of type STREAM, just like the function we want to build.

> data Flatten a x l where
>   Flatten :: x TREE -> Flatten a x STREAM
> flatten = inTerm . Flatten

> instance PFunctor (Flatten a) where
>   pmap g (Flatten x) = Flatten (g x)

> instance IsCausal (Flatten a) (G a) where
>   step' (Flatten (_ :@ Fork_ x l r)) =
>             Cons_ x (merge (flatten l) (flatten r))

To run the functions, we need to define a fixpoint of G. We
call it U for universe.

> data U a l where
>   ForkU :: a -> U a TREE -> U a TREE -> U a TREE
>   ConsU :: a -> U a STREAM -> U a STREAM

> instance Nu (G a) (U a) where
>   outNu (ForkU x l r) = Fork_ x l r
>   outNu (ConsU x xs) = Cons_ x xs
>   inNu (Fork_ x l r) = ForkU x l r
>   inNu (Cons_ x xs) = ConsU x xs

example

> extree =  f 2 (f 3 (f 5 (m 7)
>                         (m 11))
>                    (f 13 (m 17)
>                          (f 19 (f 23 (m 29)
>                                      (m 31))
>                                (m 37))))
>               (f 41 (m 43)
>                     (f 47 (m 53)
>                           (m 59)))
>  where f = ForkU
>        m n = mapT (* n) extree

> mapT :: (a -> a) -> U a TREE -> U a TREE
> mapT f (ForkU x l r) = ForkU (f x) (mapT f l) (mapT f r)

> take :: Int -> U a STREAM -> [a]
> take n s | n <= 0 = []
> take n (ConsU h t) = h : take (n - 1) t

> example n = take n $ runCausal (Flatten extree)


  Let's try and make a type that is the union of all
  coinductive types.

  We add an associated type so that the type checker can
  work out the type of 'step' for the instances of IsCausal.

> class C.Nu (BaseFunctor t) t => Coinductive t where
>   type BaseFunctor t :: * -> *

  Union of coinductive types. The types themselves serve as
indices to the GADT.

> data UC t where
>   UC :: Coinductive t => t -> UC t

> fromUC :: UC t -> t
> fromUC (UC x) = x

  Base functor for UC

> data UCF (x :: * -> *) t where
>   UCF :: Coinductive t => BaseFunctor t (x t) -> UCF x t

> instance PFunctor UCF where
>   pmap g (UCF y) = UCF (fmap g y)
>

> instance Nu UCF UC where
>   outNu (UC x) = UCF (fmap UC (C.outNu x))
>   inNu (UCF y) = UC (C.inNu (fmap fromUC y))

   Now let's revisit our previous example using UC.

> data StreamF a x = ConsF a x deriving Functor
> instance C.Nu (StreamF a) (Stream a) where
>   outNu (Cons h t) = ConsF h t
>   inNu (ConsF h t) = Cons h t
> instance Coinductive (Stream a) where
>   type BaseFunctor (Stream a) = StreamF a

> data TreeF a x = ForkF a x x deriving Functor
> instance C.Nu (TreeF a) (Tree a) where
>   outNu (Fork x l r) = ForkF x l r
>   inNu (ForkF x l r) = Fork x l r
> instance Coinductive (Tree a) where
>   type BaseFunctor (Tree a) = TreeF a

> data MergeU a x l where
>   MergeU :: x (Stream a) -> x (Stream a) -> MergeU a x (Stream a)
> mergeU = res2 inTerm MergeU

> instance PFunctor (MergeU a) where
>   pmap g (MergeU l r) = MergeU (g l) (g r)

> instance IsCausal (MergeU a) UCF where
>   step' (MergeU (_ :@ UCF (ConsF x xs)) (ys :@ _)) =
>             UCF (ConsF x (mergeU ys xs))


> data FlattenU a x l where
>   FlattenU :: x (Tree a) -> FlattenU a x (Stream a)
> flattenU = inTerm . FlattenU

> instance PFunctor (FlattenU a) where
>   pmap g (FlattenU x) = FlattenU (g x)

> instance IsCausal (FlattenU a) UCF where
>   step' (FlattenU (_ :@ UCF (ForkF x l r))) =
>             UCF (ConsF x (mergeU (flattenU l) (flattenU r)))
 

Cherry on the cake, we easily work with parametric types, and
with any numbers of parameters.

> data Apply a b x t where
>   Apply ::
>     x (Stream (a -> b)) ->
>     x (Stream a) ->
>     Apply a b x (Stream b)
>
> infixl 5 `app`
> app = inTerm `res2` Apply
>
> instance PFunctor (Apply a b) where
>   pmap n (Apply f x) = Apply (n f) (n x)
>

> instance IsCausal (Apply a b) UCF where
>   step' (Apply (_:@ UCF (ConsF f fs))
>                (_:@ UCF (ConsF x xs)))
>     = UCF (ConsF (f x) (app fs xs))


  Wouldn't it be nice if we could avoid the UCF constructor?
  The library UCausal solves this problem by defining a At type
 
> data At' x t where
>   (:@@) :: Coinductive t => x t -> BaseFunctor t (x t) -> At' x t

  and the step function becomes

  step :: forall x . f (At x) :-> UCF (Term x)

  There isn't much we can do to eliminate the UCF on the right
  hand side because it is an existential type.

  The only practical solution is to define synonyms for the
  constructors.
