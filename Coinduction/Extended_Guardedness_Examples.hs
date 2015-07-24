{- source code from extended_guardedness.tex

-}
{-# LANGUAGE 
      RankNTypes 
    , DeriveFunctor 
    , TypeOperators
    , MultiParamTypeClasses
    , FunctionalDependencies
    , FlexibleInstances
    , GADTs
--    , NoMonomorphismRestriction
 #-}

module Extended_Guardedness_Examples where

data What = What

type R = Double
type Str a = [a]
type Alg f x = f x -> x

class Functor f => Rep f t | t -> f where
  outRep :: t -> f t
  inRep :: f t -> t

type Coalg f x = x -> f x
unfold :: (Functor g, Rep g t) => Coalg g s -> s -> t
unfold c = go
  where go s = inRep $ go `fmap` c s


data T x = Plus x x         deriving Functor
data F x = R :< x     deriving Functor
infixr 5 :<
instance Rep F (Str R) where
  outRep (h:t)   = h :< t
  inRep (h :< t) = h :t


type Distr t f = forall x . t (f x) -> f (t x)

distrAlg :: (Functor t, Functor f, Rep f nuF) => Distr t f -> Alg t nuF
distrAlg lambda = it where
  it = inRep . fmap it . lambda . fmap outRep


plusDistr :: Distr T F
plusDistr ((x0 :< x') `Plus` (y0 :< y')) = x0 + x0 :< x' `Plus` y'
plus :: Str R -> Str R -> Str R
plus x y = distrAlg plusDistr $ x `Plus` y


upto :: (Functor t, Functor f, Rep f nuF) => 
  Distr t f -> (x -> f (t x)) -> x -> nuF
upto lambda gamma = f
  where
    f = inRep . fmap (b . fmap f) . gamma
    b = distrAlg lambda

data X = Str R `Times` Str R
shuffleCg :: X -> F (T X)
shuffleCg (x@(x0:x') `Times` y@(y0:y'))
  = x0 * y0 :< (x `Times` y') `Plus` (x' `Times` y)

shuffle :: Str R -> Str R -> Str R
shuffle x y = upto plusDistr shuffleCg $ x `Times` y

--------------------------------------------------
-- lambda coiteration theorem

data Free f x = Ret x | InF (f (Free f x))
   deriving Functor

foldFree :: Functor f => (x -> r) -> Alg f r -> Free f x -> r
foldFree ret inf = freeAlg inf . fmap ret

freeAlg :: Functor f => Alg f r -> Alg (Free f) r
freeAlg alg (Ret x) = x
freeAlg alg (InF y) = alg (freeAlg alg `fmap` y)


data Z
data S n
data TNat n where 
  Z :: TNat Z
  S :: TNat n -> TNat (S n)

data E t where
  E :: t n -> E t

data Iter n t x where
  IterZ :: x -> Iter Z t x
  IterS :: t (Iter n t x) -> Iter (S n) t x

data SumIter t x where
  SumIter :: TNat n -> Iter n t x -> SumIter t x

inSumIter0 :: x -> SumIter t x
inSumIter0 = SumIter Z . IterZ

-- free2sumiter :: Functor f => Free f x -> SumIter f x
-- free2sumiter (Ret x) = SumIter Z (IterZ x) 
-- free2sumiter (InF y) = sucSumIter $ fmap free2sumiter y

iter2free :: Functor f => Iter n f x -> Free f x
iter2free (IterZ x) = Ret x
iter2free (IterS y) = InF $ fmap iter2free y

sumiter2free :: Functor f => SumIter f x -> Free f x
sumiter2free (SumIter _ x) = iter2free x

iter :: Functor f =>
  (x -> r) -> 
  (f r -> r) ->
  Iter n f x -> r
iter z s  (IterZ x) = z x
iter z s  (IterS y) = s (fmap (iter z s) y)

sumIter :: Functor f =>
  (forall n . TNat n -> Iter n f x -> r) ->
  SumIter f x -> r
sumIter h (SumIter n x) = h n x

factor :: (Functor t) => (t y -> y) -> (x -> y) -> (SumIter t x -> y)
factor b f = sumIter (const $ iter f b)

phiFam :: (Functor f, Functor t) =>
  Distr t f -> (x -> f (t x)) -> Iter n t x -> f (Iter (S n) t x)
phiFam lambda phi (IterZ x) = 
  fmap (IterS . fmap IterZ) $ phi x
phiFam lambda phi (IterS y) = 
  fmap IterS $ lambda $ fmap (phiFam lambda phi) y

termCoalg :: (Functor f, Functor t) => 
  Distr t f -> (x -> f (t x)) -> Coalg f (SumIter t x)
termCoalg lambda phi = 
  sumIter (\n -> fmap (SumIter (S n)) . (phiFam lambda phi))


upto' :: (Functor t, Functor f, Rep f nuF) => 
  Distr t f -> (x -> f (t x)) -> x -> nuF
upto' lambda phi  =  unfold (termCoalg lambda phi) . inSumIter0
shuffle' :: Str R -> Str R -> Str R
shuffle' x y = upto' plusDistr shuffleCg $ x `Times` y


-- can we define termCoalg using the free algebra?

termCoalg' :: (Functor f, Functor t) => 
  Distr t f -> (x -> f (t x)) -> Coalg f (Free t x)
termCoalg' lambda phi =
  foldFree (fmap (InF . fmap Ret) . phi)
           (fmap InF . lambda)

upto'' :: (Functor t, Functor f, Rep f nuF) => 
  Distr t f -> (x -> f (t x)) -> x -> nuF
upto'' lambda phi  =  unfold (termCoalg' lambda phi) . Ret
shuffle'' :: Str R -> Str R -> Str R
shuffle'' x y = upto'' plusDistr shuffleCg $ x `Times` y


-- prove that termCoalg and termCoalg' are equivalent
phiFam1 :: (Functor f, Functor t) =>
  Distr t f -> (x -> f (t x)) -> Iter n t x -> f (Free t x)
phiFam1 l p = fmap iter2free . phiFam l p 

phiFam2 :: (Functor f, Functor t) =>
  Distr t f -> (x -> f (t x)) -> Iter n t x -> f (Free t x)
phiFam2 l p = termCoalg' l p . iter2free

{-

fmap iter2free . phiFam lambda phi  ==?==  termCoalg' lambda phi . iter2free

 *
* *

  Base case

fmap iter2free . phiFam lambda phi $ IterZ x
  =
fmap iter2free . fmap (IterS . fmap IterZ) $ phi x
  =
fmap (iter2free . IterS . fmap IterZ) $ phi x
  =
fmap (InF . fmap iter2free . fmap IterZ) $ phi x
  =
fmap (InF . fmap (iter2free . IterZ)) $ phi x
  =
fmap (InF . fmap Ret) $ phi x

 *
* *

termCoalg' lambda phi . sumiter2free $ SumIter Z (IterZ x)
  =
termCoalg' lambda phi $ Ret x
  =
fmap (InF . fmap Ret) $ phi x

 *
* *

  Induction case

fmap iter2free . phiFam lambda phi $ IterS x
  =
fmap iter2free . fmap IterS . lambda . fmap (phiFam lambda phi) $ y
  =
fmap (iter2free . IterS) . lambda . fmap (phiFam lambda phi) $ y
  =
fmap (InF . fmap iter2free) . lambda . fmap (phiFam lambda phi) $ y
  =
fmap InF . fmap (fmap iter2free) . lambda . fmap (phiFam lambda phi) $ y
  =
     { `lambda` : T.F -> F.T commutes with 
       `fmap (fmap iter2free)` by naturality }
  
fmap InF . lambda . fmap (fmap iter2free) . fmap (phiFam lambda phi) $ y
  =
fmap InF . lambda . fmap (fmap iter2free . phiFam lambda phi) $ y
  =
     { induction hypothesis }
fmap InF . lambda . fmap (termCoalg' lambda phi . iter2free) $ y


 *
* *

termCoalg' lambda phi . sumiter2free $ SumIter (S n) (IterS y)
  =
termCoalg' lambda phi . iter2free (IterS y)
  =
termCoalg' lambda phi . InF . fmap iter2free $ y
  =
fmap InF . lambda . fmap termCoalg' lambda phi . fmap iter2free $ y
  =
fmap InF . lambda . fmap (termCoalg' lambda phi . iter2free) $ y

-}


--------------------------------------------------

