Support for parametric datatypes like streams, the
implementation is virtually identical to Causal.lhs, by using
a categorical lifting.

Extended guardedness recursion by
syntactic coalgebras in a compositional way
Without the clutter of the free monad constructors.

Causal functions are best explained with sized-types: they
are size invariant: they can construct their output up to
depth `n` from the unfolding up to depth `n` of all their
inputs, for all `n`.

They are composable.

IMPORTANT: relate that with tree transducers

> {-# LANGUAGE 
>       RankNTypes 
>     , DeriveFunctor 
>     , TypeOperators
>     , MultiParamTypeClasses
>     , FlexibleInstances
>     , GADTs
>     , FunctionalDependencies
>     , ScopedTypeVariables
>     , KindSignatures
>   --   , NoMonomorphismRestriction
> #-}

> module Coinduction.CausalParam where
> import Auxiliary.Composition(res2)
> import Prelude hiding (map, zip, odd, even, iterate, repeat)
> import Control.Applicative
> import Control.Monad

> data What = What {what :: forall a . a}

fixed-point with a parameter.

 > data Fix1 g a = InFix1 {outFix1 :: g a (Fix1 g a)}



The object of the category `PType` Haskell parametric types of
kind `* -> *`. They are not required to be functorial.  The
arrows of the category are parametric functions, akin to
natural transformations, but without the structural property
since they're not between functors but between parametric
types. (Note this is a higher rank type.)

> infix 1 :->
> type a :-> b = forall p . a p -> b p

The functors from `PType` to `PType` are called
`PFunctor`. Their functorial action maps a parametric function
to another parametric function.

> class PFunctor h where
>   pmap :: u :-> v  ->  h u :-> h v


not used

> type PNatTrans f g = (PFunctor f, PFunctor g) => forall t . f t :-> g t


Algebras and coalgebras in the category of parametric types.

> type Alg g r   = g r :-> r
> type Coalg g r = r :-> g r

Rep (representation) is a Class for generic programming with
recursive datatypes with one parameter.  
Nu f must be isomorphic to t and the 
functions outRep and inRep must bijections. Provides a generic view.

> class PFunctor f => Nu f t | t -> f where
>   outNu :: Coalg f t
>   inNu  :: Alg f t

stream functor

> data StrF t h = h :< t h -- deriving Functor
> infixr 5 :< -- same precedence as (:)
> instance PFunctor StrF where
>   pmap g (h :< t) = h :< g t

> instance Nu StrF [] where
>   outNu (h:t)   = h :< t
>   inNu (h :< t) = h :t

> unfold :: (PFunctor g, Nu g t) => Coalg g s -> s :-> t
> unfold c = inNu . pmap (unfold c) . c

a type of pairs used for pattern annotations corresponding to l@(h:t)


> infixr 0 :@

At :: PFunctor -> PType -> Type

> data At f t x = t x :@ f t x

> instance (PFunctor f) => PFunctor (At f) where
>   pmap m (x :@ y) =  m x :@ pmap m y

Free :: PFunctor -> PFunctor

> data Free f t x = Var (t x) | App (f (Free f t) x)
> instance PFunctor f => PFunctor (Free f) where
>   pmap rename (Var x) = Var (rename x)
>   pmap rename (App y) = App (pmap (pmap rename) y)

> fromVar :: Free f x :-> x
> fromVar (Var x) = x
> fromVar (App _) = error "fromVar: App"
 
> foldFree :: PFunctor f => (x :-> r) -> Alg f r -> Free f x :-> r
> foldFree var app = freeAlg app . pmap var
 
> freeAlg :: PFunctor f => Alg f r -> Alg (Free f) r
> freeAlg alg (Var x) = x
> freeAlg alg (App y) = alg (freeAlg alg `pmap` y)

 
A Term is usually a data representation of the functions to
be applied to some recursive arguments.
 
Term :: PFunctor -> PType -> PType

> type Term g = Free (Causal g)
> inTerm :: (IsCausal f g) => f (Term g s) :-> Term g s
> inTerm = App . Causal


> type StrTm = Term StrF

 > type CausalAlg g r = Alg (Causal g) r
  
The primary operation is step, step' is there to make it easier
to write the definition. By automatically wrapping the
recursive elements in `Ret` to make it directly useable on
the right hand side. When defining step', it is an error to
pattern match on the Term structure of the recursive
element, because only `Ret` will ever be used.
 
> class (PFunctor f, PFunctor g) => IsCausal f g | f -> g where
>   step :: forall x . f (At g x) :-> g (Term g x)
>   step = step' . pmap (pmap Var)

>   step' :: forall x . f (At g (Term g x)) :-> g (Term g x)
>   step' = step . pmap (pmap fromVar)

Causal is an abstract datatype with the only operation necessary for
unfolding the coalgebra.

Causal :: PFunctor -> PFunctor

> data Causal g t p where
>   Causal :: IsCausal f g => f t p -> Causal g t p

Note that automatically `step` is an operation of Causal, and
together with `pmap`, are the sole operations available on
values of this type: the existential is an abstraction
mechanism that hides all the particulars of an actual value.
              
> instance PFunctor (Causal g) where
>   pmap m (Causal y) = Causal (pmap m y)

> instance (PFunctor g) => IsCausal (Causal g) g where
>   step (Causal y)  = step y
>   step' (Causal y) = step' y


But invariably we will need to use `pmap` before being able
to apply `step`, so we provide a function that does both:

> tagArg :: Coalg g s -> Coalg (At g) s
> tagArg out x = x :@ out x

> coalgStep :: IsCausal f g => 
>   Coalg g s -> f s :-> g (Term g s)

> coalgStep out fs = step (tagArg out `pmap` fs)

> type GuardedCg g s = s :-> g (Term g s)

The monomorphism restriction forces us to make the recursion
on `semGuardedCg c` rather than a local definition.

> semGuardedCg :: PFunctor g => GuardedCg g s -> Coalg g (Term g s)
> semGuardedCg c (Var s) = c s
> semGuardedCg c (App w) =   -- w :: Causal g (Term g s)
>       pmap (freeAlg App) $ coalgStep (semGuardedCg c) w -- coalgStep c' w :: g (Term g (Term g s))

> termCg :: PFunctor g => Coalg g s -> Coalg g (Term g s)
> termCg c = semGuardedCg (pmap Var . c)

> semCausal :: (Nu g t) => Alg (Term g) t
> semCausal = unfold (termCg outNu)

> runCausal :: (IsCausal f g, Nu g t) => Alg f t
> runCausal = semCausal . inTerm . pmap Var

> lambdaCoiter :: (IsCausal f g, Nu g t) => Alg f t
> lambdaCoiter = 
>   inNu . pmap (freeAlg lambdaCoiter) . step . pmap (tagArg outNu)

> runGuardedCg :: Nu g t => GuardedCg g s -> s :-> t
> runGuardedCg c y = unfold (semGuardedCg c) (Var y)
 
> upto :: Nu g t => GuardedCg g s -> s :-> t
> upto c = inNu . pmap (foldFree (upto c) lambdaCoiter) . c

Examples


Importantly, the first causal functions to recognise are the constructors!
 
> data Cons t a = Cons a (t a)

> instance PFunctor Cons where
>   pmap n (Cons h t) = Cons h (n t)
 
> infixr 5 <:
> (<:) :: a -> StrTm s a -> StrTm s a
> h <: t = inTerm $ Cons h t

> instance IsCausal Cons StrF where
>   step' (Cons h (t :@_)) = h :< t

The parameter comes into play for the map function
 
> data Map a t b = Map (a -> b) (t a)

> map = inTerm `res2` Map

> instance PFunctor (Map a) where
>   pmap n (Map f s) = Map f (n s)
 
> instance IsCausal (Map a) StrF where
>   step' (Map f (_:@ h :< t)) = f h :< map f t
                                 
no stream argument

> data Iterate (s :: * -> *) a = Iterate (a -> a) a
> iterate = inTerm `res2` Iterate

> instance PFunctor Iterate where
>   pmap n (Iterate f x) = Iterate f x

> instance IsCausal Iterate StrF where
>   step' (Iterate f x) = x :< map f (iterate f x)
 



   take 10 $ runCausal (Iterate (+3) 0)
                          
> data Repeat (t :: * -> *) a = Repeat a
> repeat = inTerm . Repeat

> instance PFunctor Repeat where
>   pmap n (Repeat x) = Repeat x

> instance IsCausal Repeat StrF where
>   step' (Repeat x) = x :< repeat x


                          
Applicative

> data Apply a t b = Apply (t (a -> b)) (t a)

> instance PFunctor (Apply a) where
>   pmap n (Apply f x) = Apply (n f) (n x)


> infixl 5 `app`
> app :: StrTm s (a -> b) -> StrTm s a -> StrTm s b
> app = inTerm `res2` Apply

> instance IsCausal (Apply a) StrF where
>   step' (Apply (_:@ f :< fs) (_:@ x :< xs))
>     = f x :< app fs xs

   take 10 $ runCausal (Apply (repeat (*10)) [1..])
   take 10 $ semCausal (app (app (Var (repeat (*))) (Var [10..])) (Var [10..]))

> lift2 op x y = repeat op `app` x `app` y

  take 10 $ semCausal (lift2 (+) (Var [1..]) (Var [100..]))

> (<+>) :: Num b => StrTm s b -> StrTm s b -> StrTm s b
> (<+>) = lift2 (+)

fibonnacci

> fib' = 0 : zipWith (+) (1 : fib') fib'

using our library to compute fibonacci is slow because there
is no sharing, the stream is being computed again and again.

we need to use a gadt because Fib is not polymorphic

> data Fib (t :: * -> *) a where
>   Fib :: Fib t Int

> fib = inTerm Fib

> instance PFunctor Fib where
>   pmap n Fib = Fib

> instance IsCausal Fib StrF where
>   step Fib = 0 :< ((1 <: fib) <+> fib)

    take 20 $ runCausal Fib
