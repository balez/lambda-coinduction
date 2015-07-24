Causal coinductive functions.

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
>       Rank2Types 
>     , DeriveFunctor 
>     , TypeOperators
>     , FunctionalDependencies
>     , FlexibleInstances
>     , GADTs
> #-}

> module Coinduction.Causal where
> import Auxiliary.Composition(res2)
> import Prelude hiding (map, zip, odd, even, iterate, zipWith)
> import qualified Prelude
> import Control.Applicative ((<$>))
> import Control.Monad

 > data What = What {what :: forall a . a}

 > data Nu g = InNu {outNu :: g (Nu g)}

Rep (representation) is a Class for generic programming with
recursive datatypes.  Nu f must be isomorphic to t and the
functions outRep and inRep must bijections. Provides a generic view.

> class Functor f => Nu f t | t -> f where
>   outNu :: t -> f t
>   inNu :: f t -> t


needs FlexibleInstances

-- > instance Functor g => Nu g (Nu g) where
-- >   outNu = outNu
-- >   inNu  = InNu

-- > unfoldNu :: Functor g => Coalg g s -> s -> Nu g
-- > unfoldNu = unfold

> type Coalg g s = s -> g s

> unfold :: (Functor g, Nu g t) => Coalg g s -> s -> t
> unfold c = go
>   where go s = inNu $ go <$> c s
 
a type of pairs used for pattern annotations corresponding to l@(h:t)

 > data a :@ b = a :@ b deriving Functor

> data At f x = x :@ f x deriving Functor

> infixr 0 :@

> type Distr f g = forall x . f (At g x) -> g (f x)


Streams: the empty list is not admitted for this type.

> type Str a = [a]

the stream functor, corresponding to the cons (:) constructor.

> data StrF h t = h :< t deriving Functor
> infixr 5 :< -- same precedence as (:)

> instance Nu (StrF a) (Str a) where
>   outNu (h:t)   = h :< t
>   inNu (h :< t) = h :t

example: zip

vector of two elements

> data V2 x = V2 x x
>   deriving Functor

> zipDistr :: Distr V2 (StrF a)
> zipDistr (V2 (l :@ x :< l') (r :@ y :< r')) = x :< V2 r l'

> type Alg f a = f a -> a

> semDistr :: Functor f => Distr f (StrF a) -> Alg f (Str a)
> semDistr d y = case d (fmap out y) of
>   h :< y' -> h : semDistr d y'    
>   where out l@(h:t) = (l :@ h :< t)


The problem with the previous definition is that it is not
modular, if I need zip as part of another coalgebra
definition, I would need to rewrite it. The idea for
compositionality is to let the result of the coalgebra to be
another functor.

IsCausal: compositional stream (or syntactic?) coalgebra it is
more flexible to have the free monad, corresponding to an
extended guardedness.

> data Free f x = Var x | App (f (Free f x))
> instance Functor f => Functor (Free f) where
>   fmap rename (Var x) = Var (rename x)
>   fmap rename (App y) = App (fmap (fmap rename) y)

> fromVar :: Free f x -> x
> fromVar (Var x) = x
> fromVar (App _) = error "fromVar: App"
 
> foldFree :: Functor f => (x -> r) -> Alg f r -> Free f x -> r
> foldFree var app = freeAlg app . fmap var
 
> freeAlg :: Functor f => Alg f r -> Alg (Free f) r
> freeAlg alg (Var x) = x
> freeAlg alg (App y) = alg (freeAlg alg <$> y)

> instance Functor f => Monad (Free f) where
>   return = Var              
>   m >>= f = foldFree f App m

A Term is usually a data representation of the functions to
be applied to some recursive arguments.

> type Term g = Free (Causal g)
> type StrTm a = Term (StrF a)


> inTerm :: (IsCausal f g) => f (Term g s) -> Term g s
> inTerm = App . Causal

the primary operation is step, step' is there to make it
easier to write the definition. By automatically wrapping the
recursive elements in `Var` to make it directly useable on
the right hand side. When defining step', it is an error to
pattern match on the Term structure of the recursive element,
because only `Var` will ever be used.  The solution is to
make the type `Term` abstract (not exporting its
representation), the user would not have the possibility to
do pattern matching.

> class (Functor f, Functor g) => IsCausal f g | f -> g where
>    step :: forall x . f (At g x) -> g (Term g x)
>    step = step' . fmap (fmap Var)

>    step' :: forall x . f (At g (Term g x)) -> g (Term g x)
>    step' = step . fmap (fmap fromVar)

Causal is an abstract datatype with the only operation necessary for
unfolding the coalgebra.

> data Causal g x where
>   Causal :: IsCausal f g => f x -> Causal g x

> instance Functor (Causal g) where
>   fmap m (Causal y) = Causal (fmap m y)

Note that automatically `step` is an operation of Causal, and
together with `fmap`, are the sole operations available on
values of this type: the existential is an abstraction
mechanism that hides all the particulars of an actual value.

IsCausal (Causal g) g

> instance Functor g => IsCausal (Causal g) g where
>   step (Causal y) = step y

But invariably we will need to use `fmap` before being able
to apply `step`, so we provide a function that does both:

> coalgStep :: IsCausal f g => 
>   Coalg g x -> f x -> g (Term g x)
> coalgStep out f = step (tagArg out <$> f)

> tagArg :: Coalg f x -> Coalg (At f) x
> tagArg out x = x :@ out x
 
 
  > joinCausal :: Functor g => Causal g (Causal g x) -> Causal g x
 
 The semantics for IsCausal flattens (interprets?) the free monad
               
    semCausal :: (Functor g, Nu g t) => Term g t -> t
    semCausal (Var x) = x
    semCausal (App w) = ?

The case for (App w) needs some explanations:
 
    w :: Causal g (Term g t)

To use the destructor coalgStep on `w`, we need to build a
`g`-coalgebra on (Term g t), from the `g`-coalgebra on `t`,
we define a function `termCg` to compute it:
 
> termCg :: Functor g => Coalg g s -> Coalg g (Term g s)
> termCg c = semGuardedCg (fmap Var . c)
             
 > termCg c = c'
 >   where              
 >    c' (Var x) = Var <$> c x
 >    c' (App w) = join <$> coalgStep c' w -- w :: Causal g (Term g s)

Now:
 
    coalgStep (termCg outNu) w :: g (Term g (Term g (Nu g)))
 
and we need to recursively apply semCausal.  First we must
`join` the two applications of `Term g` into one, using the
fact that it is a (free) monad.

This definition is guarded by the constructor `inNu`: the
fmap `<$>` duplicates the recursive calls `semCausal . join`
to all structural recursive positions in `w`. This is exactly
what guardedness means.

But perhaps define it as an unfold or futu might be more
convincing. (todo later).

 
> semCausal :: (Nu g t) => Alg (Term g) t
> semCausal = unfold (termCg outNu)

 > semCausal (Var x) = x
 > semCausal (App w) = 
 >   inNu $ semCausal . join <$> coalgStep (termCg outNu) w

> runCausal :: (IsCausal f g, Nu g t) => Alg f t
> runCausal = semCausal . inTerm . fmap Var


We get back semCausal by extension of runCausal

> semCausal' :: (Nu g t) => Alg (Term g) t
> semCausal' =  freeAlg runCausal 


Fast implementation without building the state

Now that we now our functions are productive we don't need to actually
define them as coiterations! we implement the lambda-coiteration!

> lambdaCoiter :: (IsCausal f g, Nu g t) => Alg f t
> lambdaCoiter = 
>   inNu . fmap (freeAlg lambdaCoiter) . step . fmap (tagArg outNu)

--------------------------------------------------

> data IdStr a x = IdStr x deriving Functor
> idStr :: StrTm a s -> StrTm a s
> idStr = inTerm . IdStr
> idStr'' = step . IdStr
> idStr' = step' . IdStr
> instance IsCausal (IdStr a) (StrF a) where
>   step' (IdStr (_ :@ h :< t)) = h :< t

 >   step (IdStr (_ :@ h :< t)) = h :< Var t

Importantly, the first causal functions to recognise are the constructors!

> data Cons a x = Cons a x
>   deriving Functor

> infixr 5 <:
> (<:) :: a -> StrTm a s -> StrTm a s
> (<:) = inTerm `res2` Cons

> instance IsCausal (Cons a) (StrF a) where
>   step' (Cons h (t :@_)) = h :< t

 >   step (Cons h (t :@_)) = h :< Var t



Thus we can define a prepend function that adds a finite prefix to a stream:

> data Prepend a x = Prepend [a] x
>   deriving Functor

> infixr 5 ++:
> (++:) :: [a] -> StrTm a s -> StrTm a s
> (++:) = inTerm `res2` Prepend

> instance IsCausal (Prepend a) (StrF a) where
>   step' (Prepend [] s) = idStr' s
>   step' (Prepend (h:t) (s :@ _)) = h :< foldr (<:) s t

 >   step (Prepend [] (_ :@ x :< x')) = x :< Var x'
 >   step (Prepend (h:t) (s :@ _)) = h :< t ++: Var s

 >   step (Prepend [] x) = idStr'' x
 >   step (Prepend (h:t) (s :@ _)) = h :< foldr (<:) (Var s) t

 >   step' (Prepend [] (_ :@ x :< x')) = x :< x'
 >   step' (Prepend (h:t) (s :@ _)) = h :< foldr (<:) s t


 > instance IsCausal (Prepend a) (StrF a) where
 >   step' (Prepend [] (_ :@ x :< x')) = x :< x'
 >   step' (Prepend (h:t) (s :@ _)) = h :< t ++: s



Applicative Lifting, corresponds to liftA2

> data ZipWith a x = ZipWith (a -> a -> a) x x 
>   deriving Functor

> zipWith :: (a -> a -> a) -> StrTm a s -> StrTm a s -> StrTm a s
> zipWith op l r = inTerm $ ZipWith op l r

> instance IsCausal (ZipWith a) (StrF a) where
>   step' (ZipWith op (_ :@ x :< l) (_ :@ y :< r))
>     = x `op` y :< zipWith op l r

take 10 $ runCausal (ZipWith (+) [1..] [1..])

> (<+>) :: Num a => StrTm a s -> StrTm a s -> StrTm a s
> (<+>) = zipWith (+)


> data Shuffle a x = Shuffle x x deriving Functor
> shuffle :: Num a => StrTm a s -> StrTm a s -> StrTm a s
> shuffle = inTerm `res2` Shuffle

> instance Num a => IsCausal (Shuffle a) (StrF a) where
>   step' (Shuffle (x :@ x0 :< x') (y :@ y0 :< y'))
>     = x0 * y0 :< (x `shuffle` y') <+> (x' `shuffle` x)

> data Star a x = Star x  deriving Functor
> star :: Num a => StrTm a s -> StrTm a s
> star = inTerm . Star
> instance Num a => IsCausal (Star a) (StrF a) where
>   step' (Star (s :@ h :< t)) = 1 :< t `shuffle` (star s `shuffle` star s)
 
Example with zip. `a` is a phantom type used for the IsCausal instance.
 
> data Zip a x = Zip x x
>   deriving Functor

> zip :: StrTm a s -> StrTm a s -> StrTm a s
> zip l r = inTerm $ Zip l r
 
> instance IsCausal (Zip a) (StrF a) where
>   step' (Zip (_ :@ x :< l') (r :@ _)) = x :< zip r l'


    take 10 $ runCausal $ Zip [1..] [10..]

Zip didn't really need the flexibility of using the free
monad. The next example will:
 
    iterate f (h:t) = h : map f (iterate f t)
 
We're not ready for the general map: it would have to work on
different functors. And probably we would need dependent
types to write it.

> data Map a x = Map (a -> a) x
>   deriving Functor
> map = res2 inTerm Map

> instance IsCausal (Map a) (StrF a) where
>   step' (Map f (_:@ h :< t)) = f h :< map f t

> data Iterate a x = Iterate (a -> a) x
>   deriving Functor
> iterate = res2 inTerm Iterate

> instance IsCausal (Iterate a) (StrF a) where
>   step' (Iterate f (_:@ h :< t)) = h :< map f (iterate f t)


 
   runCausal (ZipEvOdd x y) == even x `zip` odd y
 
> data ZipEvOdd a x = ZipEvOdd x x 
>   deriving Functor

> zipEvOdd = inTerm `res2` ZipEvOdd

> instance IsCausal (ZipEvOdd a) (StrF a) where
>   step' (ZipEvOdd (_ :@ x :< l') (_ :@ _ :< r')) = x :< zipEvOdd r' l'
 
phi ~(h:t)
  = h : (even (phi (odd t)) /><\ odd (phi (even t)))

in this case, phi isn't a IsCausal but a coalgebra that uses IsCausals.
We introducte a new type for that: guarded coalgebras are
not compositional, but they can use any of the IsCausal as guard
of the states.

A better name might be GuardedCg

> type GuardedCg g s = s -> g (Term g s)

The semantic is coalgebra. we must extend the domain with
guards.  The base case is our synCg, the Causal case uses
step to get the next productive layer of the coinductive output.

> semGuardedCg :: Functor g => GuardedCg g s -> Coalg g (Term g s)
> semGuardedCg c = c'
>   where 
>     c' (Var s) = c s
>     c' (App w) =   -- w :: Causal g (Term g s)
>       fmap join $ coalgStep c' w -- coalgStep c' w :: g (Term g (Term g s))


> runGuardedCg :: Nu g t => GuardedCg g s -> s -> t
> runGuardedCg c y = unfold (semGuardedCg c) (Var y)
 
> upto :: Nu g t => GuardedCg g s -> s -> t
> upto c = inNu . fmap (foldFree (upto c) lambdaCoiter) . c

back to phi

> phi_ ~(h:t)
>   = h : (even (phi_ (odd t)) /><\ odd (phi_ (even t)))

> ~(h : t) /><\ b   = h : (b /><\ t)
> even ~(h : t)     = h : odd t
> odd  ~(h : t)     = even t


 > data Phi a = Phi [a]
 > phi = Var . Phi
 > 
 > phiCg :: GuardedCg (StrF a) (Phi a)
 > phiCg (Phi (h:t)) = h :< zipEvOdd (phi (odd t)) (phi (even t))
 
> phi = Var
> phiCg :: GuardedCg (StrF a) (Str a)
> phiCg (h:t) = h :< zipEvOdd (phi (odd t)) (phi (even t))


    take 10 $ runGuardedCg phiCg (Phi [1..])
    take 10 $ Prelude.zip (runGuardedCg phiCg (Phi [1..])) (phi_ [1..])


 *
* *

> psi_ ~(h:t)
>  = h : (even (psi_ (odd t)) /><\ psi_ t)

                      
> data Psi a = Psi [a]
> psi = Var . Psi
> 
> psiCg :: GuardedCg (StrF a) (Psi a)
> psiCg (Psi (h:t)) = h :< zipEv (psi (odd t)) (psi t)

   runCausal (ZipEv x y) == even x `zip` y

> data ZipEv a x = ZipEv x x 
>   deriving Functor

> zipEv = inTerm `res2` ZipEv

> instance IsCausal (ZipEv a) (StrF a) where
>   step' (ZipEv (_ :@ x :< l') (r :@ _)) = x :< zipOdd r l'


   runCausal (ZipOdd x y) == x `zip` odd y

> data ZipOdd a x = ZipOdd x x 
>   deriving Functor

> zipOdd = inTerm `res2` ZipOdd

> instance IsCausal (ZipOdd a) (StrF a) where
>   step' (ZipOdd (_ :@ x :< l') (_ :@ _ :< r')) = x :< zipEv r' l'

    take 10 $ Prelude.zip (runGuardedCg psiCg (Psi [1..])) (psi_ [1..])

 *
* *

Nesting. see Nesting.hs

> nest_ (h:t) = h: nest_ (nest_ (even t)) /><\ t


Nest n xs corresponds to nest_^n xs

> data Nest a = Nest Integer [a]
>   deriving Functor

> nest = Var `res2` Nest

> nestCg :: GuardedCg (StrF a) (Nest a)
> nestCg (Nest n (h:t))
>     = h :< tail_nest n t

> tail_nest n s | n == 0 = nest 0 s -- same as 'fromList'
>               | n > 0  = nest (2*n) (even s) `zip` tail_nest (n-1) s

    take 10 $ Prelude.zip (runGuardedCg nestCg (Nest 1 [1..])) (nest_ [1..])
    
    all (uncurry (==)) . take 10000 $ Prelude.zip (runGuardedCg nestCg (Nest 1 [1..])) (nest_ [1..])


same but with different name

> data IterAlpha a = IterAlpha Integer [a]
>   deriving Functor

> ialpha = Var `res2` IterAlpha

> ialphaCg :: GuardedCg (StrF a) (IterAlpha a)
> ialphaCg (IterAlpha n (h:t))
>     = h :< tail_ialpha n t

> tail_ialpha n s | n == 0 = ialpha 0 s -- same as 'fromList'
>               | n > 0  = ialpha (2*n) (even s) `zip` tail_ialpha (n-1) s


 *
* *

Another definition with nested recursive calls. See Nesting6.lhs
This one is a IsCausal.

> nestor_ (h:t) = h: nestor_ (even (nestor_ t)) /><\ t

`Nestor n` corresponds to `(nestor_ . even)^n . nestor_`

> data Nestor a x = Nestor Integer x 
>   deriving Functor

> nestor = inTerm `res2` Nestor

This example illustrate nicely the need for the free monad for states.

> instance IsCausal (Nestor a) (StrF a) where
>   step' (Nestor n (_ :@ h :< t))
>     = h :< tail_nestor n t

> tail_nestor n s
>    | n == 0 = nestor 1 s `zip` s
>    | n > 0  = nestor (n+1) s `zipOdd` tail_nestor (n-1) s


    take 10 $ Prelude.zip (runCausal (Nestor 0 [1..])) (nestor_ [1..])

    all (uncurry (==)) . take 1000 $ Prelude.zip (runCausal (Nestor 0 [1..])) (nestor_ [1..])

Different names

> data BEB a x = BEB Integer x 
>   deriving Functor

> beb = inTerm `res2` BEB


> instance IsCausal (BEB a) (StrF a) where
>   step' (BEB n (_ :@ h :< t))
>     = h :< tail_beb n t

> tail_beb n s
>    | n == 0 = beb 1 s `zip` s
>    | n > 0  = beb (n+1) s `zipOdd` tail_beb (n-1) s


--------------------------------------------------

Fibonnaci

> fib_ = 0 : (1 : fib_) <+> fib_
>   where (<+>) = Prelude.zipWith (+)

using our library to compute fibonacci is slow because there
is no sharing, the stream is being computed again and again.

> data Fib x = Fib deriving Functor
> fib = inTerm Fib

> instance IsCausal Fib (StrF Integer) where
>   step Fib = 0 :< ((1 <: fib) <+> fib)

    take 20 $ runCausal Fib


A version of Fib with sharing. We define the functional A
contraction is a guardedCoalgebra polymorphic in the state:
it cannot do anything with it except duplicate it after the guard.

> type Contraction g = forall s . GuardedCg g s

> fibF :: Contraction (StrF Integer)
> fibF x = 0 :< (1 <: fib) <+> fib
>   where fib = Var x

Again, we could avoid the need to inject variables by making
the type `Term` abstract and change `Contraction g` to: 
`forall s . Coalg g (Term g s)`

Semantically, `fixpoint c = fix (upto c)` but there would be
no sharing, so we inline `upto` to explicitly share `upto c it = it`

> fixpoint :: Nu g t => Contraction g -> t
> fixpoint c = it 
>   where it = inNu . fmap (foldFree (const it) lambdaCoiter) . c $ it


> fix f = it where it = f it
                                                     
  
> fib' :: Str Integer
> fib' = fixpoint fibF
