module Auxiliary.Composition where

{- `resk m f` applies `m` to the result of `f` after `k`
arguments.

  res0 m f =  m f
  res1 m f x = m (f x)
  res2 m f x y = m (f x y)
  ...
-}

res0 :: (a -> b) -> (a -> b)
res0 = id

res1 = (.)
res2 = res1 . res1
res3 = res1 . res2
res4 = res1 . res3
res5 = res1 . res4

{- `cstk c` ignores `k` arguments and returns `c`.
  
  cst0 c = c
  cst1 c x = c
  cst2 c x y = c
  ...
-}

cst0 = id
cst1 = const
cst2 = cst1 . cst1
cst3 = cst1 . cst2
cst4 = cst1 . cst3
cst5 = cst1 . cst4


{- `argk m f`, applies `m` to the `k-th` argument of `f`
  
  arg0 m f = f
  arg1 m f x = f (m x)
  arg2 m f x y = f x (m y)
  ...
-}

arg0 = cst1 id
arg1 = flip res1
arg2 = res1 . arg1
arg3 = res1 . arg2
arg4 = res1 . arg3
arg5 = res1 . arg4

arg12    a b     = arg2 b . arg1 a 
arg123   a b c   = arg3 c . arg12 a b 
arg1234  a b c d = arg4 d . arg123 a b c 

diag1 x f = f x
diag2 x f = diag1 x f x
diag3 x f = diag2 x f x
diag4 x f = diag3 x f x
diag5 x f = diag4 x f x


{- composing res and arg 

The general type is not very useful, because it relies `w` and
`w'` being type constructors.

aroundk 
  :: (forall x y z . w x y z ... -> w' x y z ...)
  -> (forall x y z . w' x y z ... -> w x y z ...)
  -> (f' x0 y0 z0 ... -> f' x1 y1 z1 ... -> ... -> f' xk yk zk ...)
  -> (f x0 y0 z0 ... -> f x1 y1 z1 ... -> ... -> f xk yk zk ...)
-}

around 
 :: (b -> b') 
 -> (a' -> a) 
 -> (a -> b) 
 -> (a' -> b')

around b a f = b . f . a
around0 b a f = b f
around1 b a = around (around0 b a) a --  around1 == around 
around2 b a = around (around1 b a) a
around3 b a = around (around2 b a) a
around4 b a = around (around3 b a) a



{- `withk x f` partially applies `f` with `x` for the value
 of the `k-th` argument.
   
  with2 a f = \x -> f x a
  with3 a f = \x y -> f x y a
-}

with1 a f = f a       -- == flip ($)
with2 = res1 . with1  -- == flip flip
with3 = res1 . with2  -- == res2 . with1
with4 = res1 . with3
with5 = res1 . with4
with6 = res1 . with5

{- applicative reader 

   fan2 f a b x = f (a x) (b x)
   fan3 f a b c x = f (a x) (b x) (c x)
-}

app1 f g x = f x (g x)
fan1 = res1 app1 cst1 -- == res1
fan2 = res2 app1 fan1
fan3 = res3 app1 fan2
fan4 = res4 app1 fan3


{- currying 

   cur3 f x y z = f (x,y,z)
-}

cur1 = id
cur2 = flip res2 (,)
cur3 = flip res3 (,,)
cur4 = flip res4 (,,,)
cur5 = flip res5 (,,,,)

{- uncurrying
-}

unc1 f a = f a
unc2 f (a,b) = f a b
unc3 f (a,b,c) = f a b c
unc4 f (a,b,c,d) = f a b c d
unc5 f (a,b,c,d,e) = f a b c d e

{- applicative reader with curried functions fan2x correspond
to LiftAx, where the reader argument is a couple, but all the
functions are curried.  -}

app2 f g x y = f x y (g x y)
fan21 = res1 app2 cst2 -- == res2
fan22 = res2 app2 fan21
fan23 = res3 app2 fan22
fan24 = res4 app2 fan23
fan25 = res5 app2 fan24

app3 f g x y z = f x y z (g x y z)
fan31 = res1 app3 cst3 -- == res2
fan32 = res2 app3 fan31
fan33 = res3 app3 fan32
fan34 = res4 app3 fan33
fan35 = res5 app3 fan34

