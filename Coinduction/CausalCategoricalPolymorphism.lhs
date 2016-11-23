Generalisation of both `Causal` and `CausalParam` to work on
any category. We need `PolyKinds` extension.

This is still a very fragile extension. The error messages
are quite horrible.

Note, it's not exacty "any" category, because subcategories
are not possible with this approach, but they would
complicate matters by adding extra arguments everywhere: the
proofs that an object belong to the subcategory.

I realise that if i want to limit the set of objects of a
category, we cannot have a arrow `id`, instead we'd have

    > type Obj hom a = hom a a
    > class Category hom where
    >   src :: hom a b  ->  Obj hom a
    >   tgt :: hom a b  ->  Obj hom b
    >   (.) :: hom b c  ->  hom a b  ->  hom a c


and all the constructions, like `sum` and `products` must
take a identity arrow as parameter. (why?)

    > class Category hom => SumFunctor hom sum | sum -> hom where
    >   caseSum :: hom a c -> hom b c -> hom (sum a b) c
    >   inj1 :: Obj hom a -> Obj hom b -> hom a (sum a b)
    >   inj2 :: Obj hom a -> Obj hom b -> hom b (sum a b)
    >   obj1 :: Obj hom (sum a b) -> Obj hom a
    >   obj2 :: Obj hom (sum a b) -> Obj hom b


In another design, we have a class Obj for the objects of a category:

    > class Category hom => Obj hom a where
    >   id :: hom a a
    > class Category hom where
    >   (.) :: (Obj hom a, Obj hom b, Obj hom c) =>
    >          hom b c  ->  hom a b  ->  hom a c


> {-# LANGUAGE
>       RankNTypes
>     , PolyKinds
>     , TypeOperators
>     , MultiParamTypeClasses
>     , FlexibleInstances
>     , FlexibleContexts
>     , GADTs
>     , FunctionalDependencies
> #-}

> module Coinduction.CausalCategoricalPolymorphism where
> import Auxiliary.Composition(res2)

> import Prelude (($), Either(..), either, error, const, fst, snd)

 > import Prelude hiding (Functor, fmap, id, (.), map) --, zip, odd, even, iterate, repeat)

> import qualified Prelude

`What` and `what` are used for debugging.

> data What = What {what :: forall a . a}
 
a type `~>` represent the hom-sets of some category.

For some reason with ghc-7.6.2 and ghc-7.6.3 i cannot use an
operator as a type variable.

There is a problem with this definition: in some cases we
would like to define a category where `id` is not necessarily
for all `a`. This can happen for instance when 'hom a a' is a
gadt.  Such a category where not all types are objects is
actually a subcategory of haskell. A note on implementing
subcategories is given in the introduction at the top of the
file.

> class Category (hom :: k -> k -> *) where
>   id :: hom a a
>   (.) :: hom b c  ->  hom a b  ->  hom a c

a general element

 > type Elem hom a = (Category hom) => forall g . hom g a


> instance Category (->) where
>   id = Prelude.id
>   (.) = (Prelude..)
 

The object of the category `PType` Haskell parametric types of
kind `* -> *`. They are not required to be functorial.  The
arrows of the category are parametric functions, akin to
natural transformations, but without the structural property
since they're not between functors but between parametric
types. (Note this is a higher rank type.)
 
> infixr 1 :->
> newtype a :-> b = Pfun {runPfun :: Pfun a b}
> type Pfun a b = forall p . a p -> b p

> pfun1 :: (Pfun a b -> Pfun c d) -> a :-> b -> c :-> d
> pfun1 f g = Pfun $ f $ runPfun g

> pfun2 ::
>   (Pfun a b -> Pfun c d -> Pfun e f) ->
>   a :-> b -> c :-> d -> e :-> f
> pfun2 op f g = Pfun (runPfun f `op` runPfun g)

> instance Category (:->) where
>   id = Pfun id
>   (.) = pfun2 $ \g f -> g . f

Functors

> type FMap hom hom' f = forall a b . hom a b -> hom' (f a) (f b)

> class (Category hom, Category hom') =>
>       Functor hom hom' f | f -> hom hom' where
>   fmap :: FMap hom hom' f

stream functor

> instance Functor (->) (->) ((,) a) where
>   fmap g (h, t) = (h, g t)

> data StrF t h = h :< t h
> infixr 5 :< -- same precedence as (:)

> instance Functor (:->) (:->) StrF where
>   fmap = pfun1 $ \g (h :< t) -> h :< g t


Algebra and Coalgebras are over endo functors.

> type Alg hom f r = hom (f r) r
> type Coalg hom f r = hom r (f r)


 Rep (representation) is a Class for generic programming with
 recursive datatypes with one parameter.
 Nu f must be isomorphic to t and the
 functions outRep and inRep must bijections. Provides a generic view.
 
> class (Functor hom hom f) => Nu hom f t | t -> f where
>   outNu :: Coalg hom f t
>   inNu  :: Alg hom f t
 
> instance Nu (:->) StrF [] where
>   outNu = Pfun $ \(h:t) -> h :< t
>   inNu  = Pfun $ \(h :< t) -> h :t

> instance Nu (->) ((,) a) [a] where
>   outNu = \(h:t) -> (h,t)
>   inNu  = \(h,t) -> h :t

 
> unfold :: (Functor hom hom f, Nu hom f t) => Coalg hom f s -> hom s t
> unfold c = inNu . fmap (unfold c) . c


Categories with product objects
 
> class Category hom => ProductFunctor hom prod | hom -> prod where
>   pair :: hom a b -> hom a c -> hom a (prod b c)
>   p1   :: hom (prod a b) a
>   p2   :: hom (prod a b) b
>   map1 :: hom a b -> hom (prod a c) (prod b c)
>   map2 :: hom a b -> hom (prod c a) (prod c b)


Product for * types

> instance ProductFunctor (->) (,) where
>   pair f g x = (f x, g x)
>   p1 = fst
>   p2 = snd
>   map1 m (x,y) = (m x, y)
>   map2 m (x,y) = (x, m y)

Product for * -> * types

> data (a :* b) p = a p :& b p

> instance ProductFunctor (:->) (:*) where
>   pair = pfun2 $ \f g p -> f p :& g p
>   p1 = Pfun $ \ (x :& y) -> x
>   p2 = Pfun $ \ (x :& y) -> y
>   map1 = pfun1 $ \ m (x :& y) -> m x :& y
>   map2 = pfun1 $ \ m (x :& y) -> x :& m y

composition of product and a functor

> class AtFunctor hom at | at -> hom where
>   tagArg :: hom x (f x) -> hom x (at f x)
>   at1    :: hom (at f x) x
>   at2    :: hom (at f x) (f x)
>   mapAt  :: (Functor hom hom f) => hom x y -> hom (at f x) (at f y)

> infixr 0 :@
> data At f t x = t x :@ f t x
> instance AtFunctor (:->) At where
>   tagArg = pfun1 $ \f x -> x :@ f x
>   at1 = Pfun (\(x :@ y) -> x)
>   at2 = Pfun (\(x :@ y) -> y)
>   mapAt m = Pfun $ \(x :@ y) -> (runPfun m x :@ runPfun (fmap m) y)




`At hom (*) f` is the functo `Id * f` it is a type of pairs
used for pattern annotations corresponding to l@(h:t) to work
in the most general setting we can only make pairs of arrows,
not pairs of elements.

 > infixr 0 :@
 
 > data At hom prod a f x = -- (ProductFunctor hom prod) =>
 >   hom a x :@ hom a (f x)
 
 > instance (ProductFunctor hom prod, Functor hom hom f) =>
 >   Functor hom (->) (At hom prod a f) where
 >   fmap m (x :@ y) = m . x :@ fmap m . y
 
Free Functors


> class Category hom => SumFunctor hom sum | sum -> hom where
>   caseSum :: hom a c -> hom b c -> hom (sum a b) c
>   inj1 :: hom a (sum a b)
>   inj2 :: hom b (sum a b)

> instance SumFunctor (->) Either where
>   caseSum = either
>   inj1 = Left
>   inj2 = Right

> data (a :+ b) p = L (a p) | R (b p)
> instance SumFunctor (:->) (:+) where
>   caseSum = pfun2 $ \f g p -> case p of { L x -> f x; R y -> g y}
>   inj1 = Pfun L
>   inj2 = Pfun R

> class (SumFunctor hom sum) =>
>     FreeFunctor hom sum free | free -> hom sum where
>   inFree  :: hom (sum x (f (free f x))) (free f x)
>   outFree :: hom (free f x) (sum x (f (free f x)))

> data FreeP f t x = Var (t x) | App (f (FreeP f t) x)
> instance FreeFunctor (:->) (:+) FreeP  where
>   inFree = caseSum (Pfun Var) (Pfun App)
>   outFree = Pfun (\p -> case p of {Var x -> L x; App y -> R y})

> var :: FreeFunctor hom sum free => hom x (free f x)
> var = inFree . inj1
 
> app :: FreeFunctor hom sum free => hom (f (free f x)) (free f x)
> app = inFree . inj2

> fromVar :: (FreeFunctor hom sum free) => hom (free f x) x
> fromVar = caseSum id (error "fromVar: App") . outFree

`mapFree` does variable renaming. It can be used to define
the functor instance for concrete types `free`.


> mapFreeFmap :: (FreeFunctor hom sum free) =>
>   FMap hom hom f -> hom a b -> hom (free f a) (free f b)
> mapFreeFmap fmap m =
>   caseSum (var . m) (app . fmap (mapFreeFmap fmap m)) . outFree


> mapFree :: (Functor hom hom f, FreeFunctor hom sum free) =>
>   hom a b -> hom (free f a) (free f b)
> mapFree = mapFreeFmap fmap

> freeAlgMap :: (FreeFunctor hom sum free) =>
>   FMap hom hom f -> Alg hom f r -> Alg hom (free f) r
> freeAlgMap map alg = caseSum id (alg . map (freeAlgMap map alg)) . outFree

> freeAlg :: (Functor hom hom f, FreeFunctor hom sum free) =>
>   Alg hom f r -> Alg hom (free f) r
> freeAlg = freeAlgMap fmap

> foldFree :: (Functor hom hom f, FreeFunctor hom sum free) =>
>   hom v r -> Alg hom f r -> hom (free f v) r
> foldFree var app = freeAlg app . mapFree var


 A Term is usually a data representation of the functions to
 be applied to some recursive arguments.

 Term :: PFunctor -> PType -> PType

 > type Term g = FreeFunctor (Causal g)
 > inTerm :: (IsCausal f g) => f (Term g s) ~> Term g s
 > inTerm = App . Causal


 > type StrTm = Term StrF

  > type CausalAlg g r = Alg (Causal g) r

 The primary operation is step, step' is there to make it easier
 to write the definition. By automatically wrapping the
 recursive elements in `Ret` to make it directly useable on
 the right hand side. When defining step', it is an error to
 pattern match on the Term structure of the recursive
 element, because only `Ret` will ever be used.


> class ( Functor hom hom f
>       , Functor hom hom g
>       , AtFunctor hom at
>       , FreeFunctor hom sum term
>       , AbstractCausal hom sum at term g causal
>       ) =>
>    IsCausal hom sum at causal term f g | f -> hom sum at causal term g where

>   step :: forall x . hom (f (at g x)) (g (term causal x))
>   step = step' . fmap (mapAt var)

>   step' :: forall x . hom (f (at g (term causal x))) (g (term causal x))
>   step' = step . fmap (mapAt fromVar)

 Causal is an abstract datatype with the only operation necessary for
 unfolding the coalgebra.

how can i define an abstract type polymorphic in the category?

> class Exist hom f e | e -> hom f where
>   existIntro :: hom (f t) e
>   existElim :: (forall t . hom (f t) r) -> hom e r

> class ( Functor hom hom g
>       , AtFunctor hom at
>       , FreeFunctor hom sum term) =>
>     AbstractCausal hom sum at term g causal
>     | causal -> hom sum at term g where
>   absCausal :: IsCausal hom sum at causal term f g =>
>       hom (f t) (causal t)
>   elimAbsCausal
>       :: (forall f . IsCausal hom sum at causal term f g => hom (f t) r)
>       -> hom (causal t) r

> data CausalP g t p where
>   CausalP :: IsCausal (:->) (:+) At (CausalP g) FreeP f g =>
>      f t p -> CausalP g t p

> instance (Functor (:->) (:->) g) =>
>     AbstractCausal (:->) (:+) At FreeP g (CausalP g) where
>   absCausal = Pfun CausalP
>   elimAbsCausal elim = Pfun $ \(CausalP y) -> runPfun elim y

> type StrTm = FreeP (CausalP StrF)

> inTerm :: (IsCausal hom sum at causal term f g) =>
>   hom (f (term causal s)) (term causal s)
> inTerm = app . absCausal



> inTermP ::
>   IsCausal (:->) (:+) At (CausalP g) FreeP f g =>
>   f (FreeP (CausalP g) t) x -> FreeP (CausalP g) t x
> inTermP = runPfun inTerm

  Note that automatically `step` is an operation of Causal, and
  together with `fmap`, are the sole operations available on
  values of this type: the existential is an abstraction
  mechanism that hides all the particulars of an actual value.


However, we cannot directly define instances because `causal`
is a type variable, not a concrete type.

> mapCausal :: (AbstractCausal hom sum at term g causal) =>
>   hom a b -> hom (causal a) (causal b)
> mapCausal m = elimAbsCausal (absCausal . fmap m)

> stepCausal :: (AbstractCausal hom sum at term g causal) =>
>   forall x . hom (causal (at g x)) (g (term causal x))
> stepCausal = elimAbsCausal step

> mapTerm :: ( AbstractCausal hom sum at term g f
>            , FreeFunctor hom sum free) =>
>   hom a b -> hom (free f a) (free f b)
> mapTerm = mapFreeFmap mapCausal

> termAlg :: (AbstractCausal hom sum at term g causal) =>
>  Alg hom causal r -> Alg hom (term causal) r
> termAlg = freeAlgMap mapCausal

 But invariably we will need to use `fmap` before being able
 to apply `step`, so we provide a function `coalgStep` that does both:

> coalgStep :: (IsCausal hom sum at causal term f g) =>
>   Coalg hom g s -> hom (f s) (g (term causal s))
> coalgStep out = step . fmap (tagArg out)


> coalgStepCausal :: (AbstractCausal hom sum at term g causal) =>
>   Coalg hom g s -> hom (causal s) (g (term causal s))
> coalgStepCausal out = stepCausal . mapCausal (tagArg out)

> type GuardedCg hom term causal g s = hom s (g (term causal s))

> semGuardedCg :: (AbstractCausal hom sum at term g causal) =>
>   GuardedCg hom term causal g s -> Coalg hom g (term causal s)
> semGuardedCg c =
>   caseSum c (fmap (freeAlgMap mapCausal app) . coalgStepCausal (semGuardedCg c))
>   . outFree

> termCg :: (AbstractCausal hom sum at term g causal) =>
>   Coalg hom g s -> Coalg hom g (term causal s)
> termCg c = semGuardedCg (fmap var . c)

> semCausal :: ( AbstractCausal hom sum at term g causal
>              , Nu hom g t) =>
>   Alg hom (term causal) t
> semCausal = unfold (termCg outNu)

> runCausal :: ( IsCausal hom sum at causal term f g
>              , Nu hom g t) =>
>   Alg hom f t
> runCausal = semCausal . inTerm . fmap var

> lambdaCoiter :: ( IsCausal hom sum at causal term f g
>                 , Nu hom g t) =>
>   Alg hom f t
> lambdaCoiter = lambdaCoiterCausal . absCausal

> lambdaCoiterCausal :: ( AbstractCausal hom sum at term g causal
>                       , Nu hom g t) =>
>   Alg hom causal t
> lambdaCoiterCausal =
>   inNu . fmap (freeAlgMap mapCausal lambdaCoiterCausal)
>    . stepCausal . mapCausal (tagArg outNu)

> runGuardedCg :: ( AbstractCausal hom sum at term g causal
>                 , Nu hom g t) =>
>   GuardedCg hom term causal g s -> hom s t
> runGuardedCg c = unfold (semGuardedCg c) . var

> upto :: ( AbstractCausal hom sum at term g causal
>         , Nu hom g t) =>
>   GuardedCg hom term causal g s -> hom s t
> upto c = inNu . fmap (termAlg lambdaCoiterCausal . mapTerm (upto c)) . c

 Examples


 Importantly, the first causal functions to recognise are the constructors!

 > data Cons t a = Cons a (t a)

 > instance PFunctor Cons where
 >   fmap n (Cons h t) = Cons h (n t)

 > infixr 5 <:
 > (<:) :: a -> StrTm s a -> StrTm s a
 > h <: t = inTerm $ Cons h t

 > instance IsCausal Cons StrF where
 >   step' (Cons h (t :@_)) = h :< t

 The parameter comes into play for the map function

> data Map a t b = Map (a -> b) (t a)

> map :: (a -> x) -> FreeP (CausalP StrF) t a -> FreeP (CausalP StrF) t x
> map = runPfun inTerm `res2` Map

> instance Functor (:->) (:->) (Map a) where
>   fmap = pfun1 $ \n (Map f s) -> Map f (n s)

> instance IsCausal (:->) (:+) At (CausalP StrF) FreeP (Map a) StrF where
>   step' = Pfun $ \(Map f (_:@ h :< t)) -> f h :< map f t


 (take 10 $ runPfun runCausal $ Map (+2) [0..])
==> [2,3,4,5,6,7,8,9,10,11]

> runCausalP :: (IsCausal (:->) sum at causal free f g
>               , Nu (:->) g t) => f t p -> t p

> runCausalP = runPfun runCausal

> lambdaCoiterP :: (IsCausal (:->) sum at causal free f g
>               , Nu (:->) g t) => f t p -> t p

> lambdaCoiterP = runPfun lambdaCoiter
