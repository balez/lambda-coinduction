{- 9.6 Modular Datatypes with Explicit Subtyping

New approach to solve Wadler's expression problem Similar to
Alacarte.hs, but without the problem of injections.  Same
technique was used for causal functions.  We study here if it
is possible to add new operations, since in the
implementation of causal functions, only one was necessary.
-}

 {-# LANGUAGE 
       DeriveFunctor 
     , MultiParamTypeClasses
     , FunctionalDependencies
     , FlexibleInstances
     , GADTs
     , ConstraintKinds
     , KindSignatures
     , NoMonomorphismRestriction
     , TypeOperators
     , UndecidableInstances -- for superclasses
     , FlexibleContexts
 --    , IncoherentInstances 
     , OverlappingInstances -- necessary for projections to be inferred
     , ScopedTypeVariables
     , ViewPatterns
 #-}


module ModularDatatypes.Subtyping where
import Auxiliary.Composition(res2)
import Prelude hiding (getChar, putChar, readFile, writeFile)
import qualified Prelude as P
import Control.Applicative
import Control.Monad
import Control.Monad.Trans.State


{-

We create a modular signature functor by providing the arity
of each operation independently.

-}

data Val e = Val Int deriving Functor
data Add e = Add e e deriving Functor
data Mul e = Mul e e deriving Functor

data Mu f = In {out :: f (Mu f)}
type Alg f a = f a -> a
cata :: Functor f => Alg f a -> Mu f -> a
cata alg (In y) = alg $ fmap (cata alg) y



--------------------------------------------------
-- conjunction of classes

infixr 1 :^
-- UndecidableInstances, ConstraintKinds, KindSignatures
class (c f, d f) => (c :^ d) (f :: * -> *) where
instance (c f, d f) => (c :^ d) f where

--------------------------------------------------
-- dictionaries

-- a datatype that stores a class' dictionary
-- needs KindSignatures
-- data Dict c (f :: * -> *) where
--   Dict :: c f => Dict c f
data Dict c (f :: * -> *) = c f => Dict

-- isomorphism between the dictionary of a conjunction and
-- the product of each dictionary.
split :: Dict (c :^ d) f -> (Dict c f, Dict d f)
split Dict = (Dict, Dict)

glue :: (Dict c f, Dict d f) -> Dict (c :^ d) f
glue (Dict, Dict) = Dict

infix 0 :<
class c :< d  where
  proj :: Dict d f -> Dict c f
instance c :< c where
  proj = id
instance c :< (c :^ d) where
  proj d = fst (split d)
instance (c :< d) => c :< (c' :^ d) where
  proj d = proj (snd (split d))

--------------------------------------------------

-- the difference from AlacarteReloaded2, the class parameter
-- is replaced by a dictionnary, with hope to deal with
-- subtyping more easily.
data Abstract c x where
  Abs :: Functor f => Dict c f -> f x -> Abstract c x

-- we use this instance for the terms (free monad)
instance Functor (Abstract c) where
  fmap m (Abs c y) = Abs c (fmap m y)

type Expr c = Mu (Abstract c)

-- specialisation of abstract types
spec :: (c :< d) => Abstract d x -> Abstract c x
spec (Abs d y) = Abs (proj d) y


--------------------------------------------------
-- constructing values

-- all types are inferred with NoMonomorphismRestriction
  
{- the equivalent from alacarte is 

   inject :: f :<: g => f (Expr g) -> Expr g 

we can read `c f` like a predicate.
the advantage is there is no imposed order, like there is
on `g`: it must be a right parenthesized sum.

in the original alacarte the polymorphic types are inferred
too with NoMonomorphismRestriction but nothing can be
executed until an instance of `g` is given.

-}

inExpr :: (c f, Functor f) =>     
  f (Expr c) -> Expr c
inExpr =  In . Abs Dict

val :: (c Val) => Int -> Expr c
add :: (c Add) => Expr c -> Expr c -> Expr c
mul :: (c Mul) => Expr c -> Expr c -> Expr c

val = inExpr . Val
add = inExpr `res2` Add
mul = inExpr `res2` Mul

ex1 :: (c Mul, c Val, c Add) => Expr c
ex1 = val 80 `mul` (val 5 `add`  val 4)

--------------------------------------------------
-- operations

-- the type is inferred
class Eval f where
  eval' :: (Eval :< c) => f (Expr c) -> Int

-- the pattern match on the dictionary brings into scope the fact that
-- y :: f x where Eval f  
-- it doesn't seem possible to abstract the pattern match in a function.

-- ScopedTypeVariables
eval :: (Eval :< c) => Expr c -> Int
--eval (In (spec -> Abs Dict y :: Abstract Eval (Expr c))) = eval' y

eval (In (Abs c y)) = case proj c of 
  (Dict :: Dict Eval f) -> eval' y

-- specialisation that forces the type of a polymorphic
-- expression.  

evalS :: Expr Eval -> Int
evalS = eval

instance Eval Val where
  eval' (Val x) = x

instance Eval Add where
  eval' (Add x y) = eval x + eval y

instance Eval Mul where
  eval' (Mul x y) = eval x * eval y

{- now a an expression MUST be specialised before being evaluated:
   we commit to a choice of projections
  
   eval (ex1 :: Expr Eval) ==> 720

   to this end we provide evalS which expect Expr Eval:

   evalS ex1 ==> 720

   this is not possible with the original alacarte approach.
-}

ex0 :: (c Add, c Val) => Expr c
ex0 = val 1 `add` val 2

ex0Eval :: Expr Eval
ex0Eval = ex0

{- it's always possible to use new constructors that weren't
   used in an expression, as long as they belong to the same class

however it's not possible in the original Alacarte, when the
type is specialised.

-}

ex0add2 :: (c Mul, c Add, c Val) => Expr c
ex0add2 = ex0 `mul` val 2

ex0Evaladd2 :: Expr Eval
ex0Evaladd2 = ex0Eval `mul` val 2


--------------------------------------------------
-- evaluating using an algebra
-- notice that we do not need the constraint 
-- (c :~ d, d :> EvalA) since we do not use the type `Expr c`.

class EvalAlg f where
  evalAlg' :: f Int -> Int

-- the pattern match on the dictionary brings into scope the fact that
-- y :: f x where EvalAlg f  
-- it doesn't seem possible to abstract the pattern match in a function.

-- ScopedTypeVariables
eval2 :: (EvalAlg :< c) => Expr c -> Int
eval2 (In (Abs c y)) = case proj c of 
  (Dict :: Dict EvalAlg f) -> evalAlg' (fmap eval2 y)

-- specialisation
eval2S :: Expr EvalAlg -> Int
eval2S = eval2

instance EvalAlg Val where
  evalAlg' (Val x) = x

instance EvalAlg Add where
  evalAlg' (Add x y) = x + y

instance EvalAlg Mul where
  evalAlg' (Mul x y) = x * y


-- --------------------------------------------------

class Render f where
  render' :: (Render :< c) => f (Expr c) -> String
  
-- the pattern match on the dictionary brings into scope the fact that
-- y :: f x where Render f  

-- the type is inferred
render :: (Render :< c) => Expr c -> String
render (In (Abs c y)) = case proj c of 
  (Dict :: Dict Render f) -> render' y

-- specialisation
renderS :: Expr Render -> String
renderS = render

instance Render Val where
  render' (Val i) = show i
instance Render Add where
  render' (Add x y) = "(" ++ render x ++ " + " ++ render y ++ ")"
instance Render Mul where
  render' (Mul x y) = "(" ++ render x ++ " * " ++ render y ++ ")"


-- render (ex1 :: Expr Render) ==> "(80 * (5 + 4))"
-- renderS ex1   


  
ex1EvalRender :: Expr (Eval :^ Render)
ex1EvalRender = ex1

-- eval ex1EvalRender
-- render ex1EvalRender

example2 :: String
example2 = render ex1EvalRender ++ " == " ++ show (eval ex1EvalRender)
-- ==> "(80 * (5 + 4)) == 720"

ex2 x = render x ++ " == " ++ show (eval x)


--------------------------------------------------
-- //////////////////////////////////////////////////
-- example from the alacarte article, 
-- distributing Mul over Add
-- not so easy, we need pattern matching on the abstract datatype!
-- the only way is to introduce a new operation:

class MatchAdd f where
  matchAdd' :: f x -> Maybe (x, x)
  
-- ScopedTypeVariables
matchAdd :: (MatchAdd :< c) => 
  Expr c -> Maybe (Expr c, Expr c)
matchAdd (In (Abs c y)) = case proj c of 
  (Dict :: Dict MatchAdd f) -> matchAdd' y

instance MatchAdd Add where
  matchAdd' (Add x y) = Just (x, y)
instance MatchAdd f where 
  matchAdd' = const Nothing

-- with overlapping instances we can avoid to
-- write all the cases.

-- instance MatchAdd Val where
--   matchAdd' (Val i) = Nothing
-- instance MatchAdd Mul where
--   matchAdd' (Mul x y) = Nothing


--------------------------------------------------

-- we need the new constraint `c f` so that we can build `Expr c`
--   
-- we also need for implementing `Distr Mul` 
-- the constraints `d :> MatchAdd` to do a pattern matching
-- and `c Add` to build a term using `add`

class Distr f where
  distr' :: (c Add, c f, Distr :< c, MatchAdd :< c) =>
    f (Expr c) -> Expr c

{- we need to prove the constraints 
 - Distr f
 - c f
 -}

distr :: (c Add, Distr :< c, MatchAdd :< c) => 
  Expr c -> Expr c
distr (In (Abs c y)) = case proj c of 
  (Dict :: Dict Distr f) -> case c of
    (Dict :: Dict c f) -> distr' y

-- need to bring to context the constraint `c Val` to build an `Expr c`
instance Distr Val where
  distr' (Val i) = val i
   
instance Distr Add where
  distr' (Add x y) = distr x `add` distr y

instance Distr Mul where
   distr' (Mul x y) =  distr x `dMul` distr y
     where
      dMul x (matchAdd -> Just (y, z)) = dMul x y `add` dMul x z
      dMul (matchAdd -> Just (x, y)) z = dMul x z `add` dMul y z
      dMul x y                         = x `mul` y


-- using it !
type ExprERMD = Expr (Eval :^ Render :^ MatchAdd :^ Distr)
ex1DistrMER :: ExprERMD
ex1DistrMER = ex1

-- eval ex1DistrMER
-- render ex1DistrMER

-- inferred
showDistr :: (c Add, Distr :< c, MatchAdd :< c, Eval :< c, Render :< c) 
  => Expr c -> String
showDistr x = show (eval x) ++ " = " ++ render x 
              ++ " = " ++ render x' ++ " = " ++ show (eval x')
 where
   x' = distr x

showDistrS :: ExprERMD -> String
showDistrS = showDistr

-- showDistr ex1 ==> 
--   "720 = (80 * (5 + 4)) = ((80 * 5) + (80 * 4)) = 720"
ex152 :: (c Mul, c Add, c Val) => Expr c
ex152 = mul (add (mul (val 4) (add (val 1) (val 2))) 
             (val 7)) (add (val 3) (val 5))
-- showDistr ex152
-- "152 = (((4 * (1 + 2)) + 7) * (3 + 5)) = (((((4 * 1) * 3) + ((4 * 2) * 3)) + (7 * 3)) + ((((4 * 1) * 5) + ((4 * 2) * 5)) + (7 * 5))) = 152"

-----------------------------------------------------
-- //////////////////////////////////////////////////


-- free monad

{-
data Free f x = Pure x | Effect (f (Free f x))
  deriving Functor

foldFree :: Functor f => (x -> r) -> Alg f r -> Free f x -> r
foldFree ret inf (Pure x) = ret x
foldFree ret inf (Effect y) = inf (foldFree ret inf <$> y)

instance Functor f => Monad (Free f) where
  return = Pure              
  m >>= f = foldFree f Effect m

type Term c = Free (Abstract c)
-}


-- For a better type inference we specialise the free monad
-- on the functor `Abstract c`
  
data Term c x = Pure x | Effect (Abstract c (Term c  x))
  deriving Functor
 
foldTerm :: (x -> r) -> Alg (Abstract c) r -> Term c x -> r
foldTerm pure effect (Pure x)   = pure x
foldTerm pure effect (Effect y) = effect (foldTerm pure effect <$> y)

instance Monad (Term c) where
  return = Pure
  m >>= f = foldTerm f Effect m


inTerm :: (c f, Functor f) => 
  f (Term c x) -> Term c x

inTerm = Effect . Abs Dict

-- example: calculator (from the article)


data Incr t = Incr Int t            deriving Functor
data Recall t = Recall (Int -> t)   deriving Functor

incr :: (c Incr) => Int -> Term c ()
recall :: (c Recall) => Term c Int

incr i = inTerm (Incr i (Pure ()))
recall = inTerm (Recall Pure)

-- type is inferred
tick :: (c Recall, c Incr) => Term c Int
tick = do y <- recall
          incr 1
          return y

type Mem = Int

class Run f where
   run' :: (Run :< c) => 
      f (Term c x) -> State Mem x

run :: (Run :< c) => Term c x -> State Mem x
run (Pure x) = return x
run (Effect (Abs c y)) = case proj c of 
  (Dict :: Dict Run f) -> run' y

runS :: Term Run a -> Mem -> (a, Mem)
runS = runState . run 

instance Run Incr where
  run' (Incr i x) = withState (+i) (run x)
instance Run Recall where
  run' (Recall r) = get >>= (run . r)


-- runS tick 4 ==> (4,5)

--------------------------------------------------
-- IO

data Teletype a
   = GetChar (Char -> a)
   | PutChar Char a
     deriving Functor

data FileSystem a =
     ReadFile FilePath (String -> a)
   | WriteFile FilePath String a
     deriving Functor

getChar :: (c Teletype) => Term c Char
putChar :: (c Teletype) => Char -> Term c ()
readFile ::  (c FileSystem) => FilePath -> Term c String
writefile :: (c FileSystem) => FilePath -> String -> Term c ()


getChar       = inTerm $ GetChar Pure
putChar c     = inTerm $ PutChar c (Pure ())
readFile p    = inTerm $ ReadFile p Pure
writefile p s = inTerm $ WriteFile p s (Pure ())

class Exec f where
  exec' :: (Exec :< c) => 
      f (Term c r) -> IO r

exec :: (Exec :< c) =>
  Term c r -> IO r
exec (Pure x) = return x
exec (Effect (Abs c y)) = case proj c of 
  (Dict :: Dict Exec f) -> exec' y


execS :: Term Exec a -> IO a
execS = exec


instance Exec Teletype where
  exec' (GetChar r) = P.getChar >>= (exec . r)
  exec' (PutChar c p) = P.putChar c >> exec p

instance Exec FileSystem where
  exec' (ReadFile p r) = P.readFile p >>= (exec . r)
  exec' (WriteFile p s io) = P.writeFile p s >> exec io

-- inferred
cat :: (c FileSystem, c Teletype) => FilePath -> Term c ()
cat fp = do
  contents <- readFile fp
  mapM putChar contents
  return ()

{- further work

   parametric compositional data types.
-}
