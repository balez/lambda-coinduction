Causal coinductive functions over the universe of all
coinductive types.

A causal function is a function from coinductive types to
coinductive types such that any prefix of its output is
determined by smaller or equal prefixes of its input.

Compared to Causal.lhs, this file allows to define causal
functions that work over many types, including parametric
functions. The principles are worked out in MixedDatatypes.
This version is a specialisation of MixedDatatype for better
integration of the DSL. (less clutter in syntax)


> {-# LANGUAGE
>       Rank2Types
>     , DeriveFunctor
>     , TypeOperators
>     , FunctionalDependencies
>     , FlexibleInstances
>     , GADTs
>     , TypeFamilies
>     , FlexibleContexts
> #-}

> module Coinduction.UCausal where
> import Auxiliary.Composition(res2,res3)
> import Prelude hiding (map, zip, odd, even, iterate, repeat)
> import Control.Applicative
> import Control.Monad


`ExpectedTypeOf` and `inferredTypeOf` are used in the
interactive session to obtain type information from the
typechecker.

> data Unknown = ExpectedTypeOf {inferredTypeOf :: forall a . a}
> expectedTypeOf = ExpectedTypeOf

The object of the category `PType` Haskell parametric types of
kind `* -> *`. They are not required to be functorial.  The
arrows of the category are parametric functions, akin to
natural transformations, but without the structural property
since they're not between functors but between parametric
types. (Note this is a higher rank type.)

> infix 1 :->
> type a :-> b = forall t . a t -> b t

The functors from `PType` to `PType` are called
`PFunctor`. Their functorial action maps a parametric function
to another parametric function.

> class PFunctor h where
>   pmap :: u :-> v  ->  h u :-> h v

Algebras and coalgebras in the category of parametric types.

> type PAlg g r   = g r :-> r
> type PCoalg g r = r :-> g r

Nu is a Class for generic programming with recursive
datatypes with one parameter.  `Nu f' must be isomorphic to
`t' and the functions outRep and inRep must
bijections. Provides a generic view.

> class PFunctor f => Nu f t | t -> f where
>   outNu :: PCoalg f t
>   inNu  :: PAlg f t

Coiteration of a coalgebra.

> unfold :: (PFunctor g, Nu g t) => PCoalg g s -> s :-> t
> unfold c = inNu . pmap (unfold c) . c

Greatest fixpoints for types of kind `*'.

> class Functor (BaseFunctor t) => Coinductive t where
>   type BaseFunctor t :: * -> *
>   outC :: t -> BaseFunctor t t
>   inC :: BaseFunctor t t -> t

Union of coinductive types

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
>   outNu (UC x) = UCF (fmap UC (outC x))
>   inNu (UCF y) = UC (inC (fmap fromUC y))

 A Type of pairs used for pattern annotations corresponding to l@(h:t)

> infixr 0 :@

 At :: PType -> PType

> data At x t where
>   (:@) :: Coinductive t => x t -> BaseFunctor t (x t) -> At x t

> instance PFunctor At where
>   pmap m (x :@ y) = m x :@ fmap m y

 Free :: PFunctor -> PFunctor

> data Free f x t = Var! (x t) | App! (f (Free f x) t)
> instance PFunctor f => PFunctor (Free f) where
>   pmap rename (Var x) = Var (rename x)
>   pmap rename (App y) = App (pmap (pmap rename) y)

> fromVar :: Free f x :-> x
> fromVar (Var x) = x
> fromVar (App _) = error "fromVar: App"

> foldFree :: PFunctor f => (x :-> r) -> PAlg f r -> Free f x :-> r
> foldFree var app = freeAlg app . pmap var

> freeAlg :: PFunctor f => PAlg f r -> PAlg (Free f) r
> freeAlg alg (Var x) = x
> freeAlg alg (App y) = alg (freeAlg alg `pmap` y)


  A Term is a data representation of the causal functions to
  be applied to some recursive arguments.

  Term :: PType -> PType

> type Term = Free Causal

> inTerm :: (IsCausal f) => f (Term x) :-> Term x
> inTerm = App . Causal


  The primary operation is step, step' is there to make it easier
  to write the definition. By automatically wrapping the
  recursive elements in `Ret` to make it directly useable on
  the right hand side. When defining step', it is an error to
  pattern match on the Term structure of the recursive
  element, because only `Ret` will ever be used.
 
> class (PFunctor f) => IsCausal f where
>   step :: forall x . f (At x) :-> UCF (Term x)
>   step = step' . pmap (pmap Var)

>   step' :: forall x . f (At (Term x)) :-> UCF (Term x)
>   step' = step . pmap (pmap fromVar)


  Causal is an abstract datatype with the only operation necessary for
  unfolding the coalgebra.

  Causal :: PFunctor -> PFunctor

> data Causal x t where
>   Causal :: IsCausal f => f x t -> Causal x t

  Note that automatically `step` is an operation of Causal, and
  together with `pmap`, are the sole operations available on
  values of this type: the existential is an abstraction
  mechanism that hides all the particulars of an actual value.
 
> instance PFunctor Causal where
>   pmap m (Causal y) = Causal (pmap m y)

> instance IsCausal Causal where
>   step (Causal y)  = step y
>   step' (Causal y) = step' y

  But invariably we will need to use `pmap` before being able
  to apply `step`, so we provide a function that does both:
  `coalgStep`.

> type Cg s = PCoalg UCF s
> tagArg :: Cg s -> PCoalg At s
> tagArg out x = case out x of UCF y -> x :@ y

> coalgStep :: IsCausal f =>
>   Cg s -> f s :-> UCF (Term s)
> coalgStep out fs = step (tagArg out `pmap` fs)
 
> type GuardedCg s = s :-> UCF (Term s)

  The monomorphism restriction forces us to make the recursion
  on `semGuardedCg c` rather than a local definition.

> semGuardedCg :: GuardedCg s -> Cg (Term s)
> semGuardedCg c (Var s) = c s
> semGuardedCg c (App w) =   -- w :: Causal g (Term s)
>       pmap (freeAlg App) $ coalgStep (semGuardedCg c) w -- coalgStep c' w :: g (Term (Term s))
 
> termCg :: Cg s -> Cg (Term s)
> termCg c = semGuardedCg (pmap Var . c)
 
> semCausal :: PAlg Term UC
> semCausal = unfold $ termCg outNu

> runCausal :: (IsCausal f) => f UC t -> t
> runCausal = fromUC . semCausal . inTerm . pmap Var
 
> lambdaCoiter :: (IsCausal f) => PAlg f UC
> lambdaCoiter =
>   inNu . pmap (freeAlg lambdaCoiter) . step . pmap (tagArg outNu)

> runLC :: IsCausal f => f UC t -> t
> runLC y = fromUC $ lambdaCoiter y

> unfoldGC' :: GuardedCg s -> s :-> UC
> unfoldGC' c y = unfold (semGuardedCg c) (Var y)

> unfoldGC :: GuardedCg s -> s t -> t
> unfoldGC c y = fromUC $ unfoldGC' c y

> upto' :: GuardedCg s -> s :-> UC
> upto' c = inNu . pmap (foldFree (upto' c) lambdaCoiter) . c

> upto :: GuardedCg s -> s t -> t
> upto c y = fromUC $ upto' c y

* Fixpoint of a contraction

A contraction corresponds to a strictly causal function in
the context of streams. It is a function such that any prefix
of output, is always determined by a strictly smaller prefix
of input. This property is enough to ensure that the fixpoint
is productive.

State of a contraction, marks the recursive call of type 't'

> data Rec t x t' where
>   Rec :: x t -> Rec t x t

The range is quantified over all t', yet only when t'=t will
there ever be a value. This is because the type Rec t x t' is empty
except when t'=t.

> unRec :: Rec t x t' -> x t'
> unRec (Rec y) = y

A contraction is a guarded coalgebra whose state is
universally quantified, as a result, nothing can be done with
the state except build a variable. This variable is used to
mark recursive calls. In addition, the state is empty except
when the index corresponds to the type 't' of the fixpoint,
this ensures that only variables of type 't' can ever be used.

> type Contraction' t = forall x . GuardedCg (Rec t x)

To build the fixpoint, we must replace the variables of type
't' with the fixpoint itself. In the parametric setting,
variables can have type 'x t' for any 't', but here we know
by construction that the variables can only be 'x t' for a
single 't'.

> fixpoint' :: Contraction' t -> UC t
> fixpoint' c = it
>   where it = inNu . pmap (foldFree unRec lambdaCoiter) . c $  Rec it

Since recursive calls are marked with variables, we provide a
variation where the input is already a variable.  Note that
the constructor "Var" is strict therefore we cannot build an
undefined variable (Var undefined) that could otherwise have
any type.

> type Contraction t = forall x . Term x t -> UCF (Term x) t

> semContraction :: Contraction t -> Contraction' t
> semContraction c x@(Rec _) = c (Var x)

> fixpoint :: Contraction t -> UC t
> fixpoint c = fixpoint' (semContraction c)
 
Examples

> data Stream a = a :< Stream a
>
> data StreamF a x = a :<: x deriving Functor
> instance Coinductive (Stream a) where
>   type BaseFunctor (Stream a) = StreamF a
>   outC (h :< t) = h :<: t
>   inC (h :<: t) = h :< t

This smart constructor is used on the right hand side of a step equation.

> x <| xs = UCF (x :<: xs)

A polymorphic causal function

> data Apply a b x t where
>   Apply ::
>     x (Stream (a -> b)) ->
>     x (Stream a) ->
>     Apply a b x (Stream b)
>
> infixl 5 `apply`
> apply = inTerm `res2` Apply
>
> instance PFunctor (Apply a b) where
>   pmap n (Apply f x) = Apply (n f) (n x)
>
> instance IsCausal (Apply a b) where
>   step' (Apply (_:@ f :<: fs)
>                (_:@ x :<: xs))
>     = f x <| apply fs xs

Constructors are strictly causal: they do not inspect the pattern.

> data Cons a x t where
>   Cons :: a -> x (Stream a) -> Cons a x (Stream a)
>
> instance PFunctor (Cons a) where
>   pmap m (Cons h t) = Cons h (m t)

> infixr 5 <:
> (<:) :: a -> Term x (Stream a) -> Term x (Stream a)
> (<:) = inTerm `res2` Cons

> instance IsCausal (Cons a) where
>   step' (Cons h (t :@_)) = h <| t

Merging two streams by alterning their elements.

> data Merge a x t where
>   Merge :: x (Stream a) -> x (Stream a) -> Merge a x (Stream a)
> merge = res2 inTerm Merge

> instance PFunctor (Merge a) where
>   pmap g (Merge l r) = Merge (g l) (g r)

> instance IsCausal (Merge a) where
>   step' (Merge (_:@ x :<: xs) (ys :@_)) =
>             x <| merge ys xs

trees

> data Tree a = Fork a (Tree a) (Tree a)
> data TreeF a x = ForkF a x x deriving Functor
> instance Coinductive (Tree a) where
>   type BaseFunctor (Tree a) = TreeF a
>   outC (Fork x l r) = ForkF x l r
>   inC (ForkF x l r) = Fork x l r
>

constructors

> data ForkC a x t where
>   ForkC :: a -> x (Tree a) -> x (Tree a) -> ForkC a x (Tree a)
>
> instance PFunctor (ForkC a) where
>   pmap m (ForkC x l r) = ForkC x (m l) (m r)

> fork :: a -> Term x (Tree a) -> Term x (Tree a) -> Term x (Tree a)
> fork = inTerm `res3` ForkC

This smart constructor is used on the right hand side of a
step equation.

> fork' x l r = UCF (ForkF x l r)

> instance IsCausal (ForkC a) where
>   step' (ForkC x (l :@_) (r :@_)) = fork' x l r

Flatten a tree into a stream

> data Flatten a x l where
>   Flatten :: x (Tree a) -> Flatten a x (Stream a)
> flatten = inTerm . Flatten

> instance PFunctor (Flatten a) where
>   pmap g (Flatten x) = Flatten (g x)

> instance IsCausal (Flatten a) where
>   step' (Flatten (_:@ ForkF x l r)) =
>     x <| merge (flatten l) (flatten r)

Map on trees

> data MapT a b x t where
>   MapT :: (a -> b) -> x (Tree a) -> MapT a b x (Tree b)
> mapT = res2 inTerm MapT

> instance PFunctor (MapT a b) where
>   pmap g (MapT f x) = MapT f (g x)

> instance IsCausal (MapT a b) where
>   step' (MapT f (_:@ ForkF x l r)) =
>     fork' (f x) (mapT f l) (mapT f r)

Defining a tree.  Note, that this definition is inefficient
because there is no sharing, thus the tree is recomputed in
every recursive call.

> data ExTree (x :: * -> *) t where
>   ExTree :: ExTree x (Tree Int)

> instance PFunctor ExTree where
>   pmap m ExTree = ExTree

> instance IsCausal ExTree where
>   step' ExTree =
>     fork' 1 (f 2 (f 3 (m 5)
>                       (m 7))
>                  (f 11 (m 13)
>                        (f 17 (f 19 (m 23)
>                                    (m 29))
>                              (m 31))))
>             (f 37 (m 41)
>                   (f 43 (m 47)
>                         (m 53)))
>    where f = fork
>          m n = mapT (* n) (inTerm ExTree)

For a more efficient definition, we define "extree" as a
fixpoint.

> extreeF :: (Num a) => Contraction (Tree a)
> extreeF x =
>     fork' 1 (f 2 (f 3 (m 5)
>                       (m 7))
>                  (f 11 (m 13)
>                        (f 17 (f 19 (m 23)
>                                    (m 29))
>                              (m 31))))
>             (f 37 (m 41)
>                   (f 43 (m 47)
>                         (m 53)))
>    where f = fork
>          m n = mapT (* n) x

> extree = fromUC $ fixpoint extreeF

> takeS :: Int -> Stream a -> [a]
> takeS n s | n <= 0 = []
> takeS n (h :< t) = h : takeS (n - 1) t

> runFlatten t = runLC $ Flatten (UC t)

> example n = takeS n $ runFlatten (runLC ExTree)
> example' n = takeS n $ runFlatten extree
