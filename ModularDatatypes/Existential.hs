{-  New approach to solve Wadler's expression
problem Similar to alacarte, but without the problem of
injections.  Same technique was used for causal functions.
We study here if it is possible to add new operations, since
in the implementation of causal functions, only one was necessary 
-}

 {-# LANGUAGE 
       DeriveFunctor 
--     , FlexibleInstances
     , GADTs
     , ConstraintKinds
 #-}


module ModularDatatypes.Existential where
import Auxiliary.Composition(res2)

{-

We create a modular signature functor by providing the arity
of each operation independently.

-}

data Val e = Val Int deriving Functor
data Add e = Add e e deriving Functor
data Mul e = Mul e e deriving Functor

data Fix f = In {out :: f (Fix f)}
type Alg f a = f a -> a

-- needs  `ConstraintKinds` for `c`
data Abstract c x where
  Abs :: (Functor f, c f) => f x -> Abstract c x

instance Functor (Abstract c) where
  fmap m (Abs y) = Abs (fmap m y)


type Expr c = Fix (Abstract c)

-- all types are inferred with NoMonomorphismRestriction
inAbs :: (Functor f, c f) => f (Expr c) -> Expr c
inAbs =  In . Abs

val :: (c Val) => Int -> Expr c
add :: (c Add) => Expr c -> Expr c -> Expr c
mul :: (c Mul) => Expr c -> Expr c -> Expr c

val = inAbs . Val
add = inAbs `res2` Add
mul = inAbs `res2` Mul


example1 :: (c Mul, c Val, c Add) => Expr c
example1 = val 80 `mul` (val 5 `add`  val 4)
--------------------------------------------------
-- operations

class Eval f where
  evalAlg :: f Int -> Int

eval :: Expr Eval -> Int
eval (In (Abs y)) = evalAlg $ fmap eval y

instance Eval Val where
  evalAlg (Val x) = x
instance Eval Add where
  evalAlg (Add x y) = x + y
instance Eval Mul where
  evalAlg (Mul x y) = x * y


--------------------------------------------------

class Render f where
   render' :: f (Expr Render) -> String


{-
instance Render (Abstract Render) where
  render' (Abs y) = render' y
-- inferred
render :: Expr Render -> String
render (In x) = render' x

-}

render :: Expr Render -> String
render (In (Abs y)) = render' y


instance Render Val where
   render' (Val i) = show i
instance Render Add where
   render' (Add x y) = "(" ++ render x ++ " + " ++ render y ++ ")"
instance Render Mul where
   render' (Mul x y) = "(" ++ render x ++ " * " ++ render y ++ ")"

example2 :: String
example2 = render example1 ++ " == " ++ show (eval example1)

--ex2 x = render x ++ " == " ++ show (eval x)


{- only problem: when the values are polymorphic, they're not
   in constructor form and each function call, like `render`
   or `eval` would allocate the same isomorphic term representation.
   the only possibility is to specialise it by giving it a type, but
 this restricts further use of it (the operations that it can be used with).
-}

ex1Render :: Expr Render
ex1Render = example1

{- now, we cannot eval ex1, only render it.  It would be good
to be able to choose a specialisation a la carte. and thus
build the constructor normal form only once, when all its usage is known.
-}
