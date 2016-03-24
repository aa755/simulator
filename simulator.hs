{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Simulator where

import qualified Prelude
import qualified Data.Bits
import qualified Data.Ratio
import qualified Data.Char

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
import qualified GHC.Prim
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Prim.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

false_rect :: a1
false_rect =
  Prelude.error "absurd case"

false_rec :: a1
false_rec =
  false_rect

fst :: ((,) a1 a2) -> a1
fst p =
  case p of {
   (,) x0 _ -> x0}

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) _ y0 -> y0}

app :: (([]) a1) -> (([]) a1) -> ([]) a1
app l m =
  case l of {
   ([]) -> m;
   (:) a l1 -> (:) a (app l1 m)}

compOpp :: Prelude.Ordering -> Prelude.Ordering
compOpp r =
  case r of {
   Prelude.EQ -> Prelude.EQ;
   Prelude.LT -> Prelude.GT;
   Prelude.GT -> Prelude.LT}

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
data SigT a p =
   ExistT a p

proj1_sig :: a1 -> a1
proj1_sig e =
  e

projT1 :: (SigT a1 a2) -> a1
projT1 x0 =
  case x0 of {
   ExistT a _ -> a}

projT2 :: (SigT a1 a2) -> a2
projT2 x0 =
  case x0 of {
   ExistT _ h -> h}

sumbool_rect :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rect f f0 s =
  case s of {
   Prelude.True -> f __;
   Prelude.False -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rec =
  sumbool_rect

sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub = (\n m -> Prelude.max 0 (n Prelude.- m))

compose :: (a2 -> a3) -> (a1 -> a2) -> a1 -> a3
compose g f x0 =
  g (f x0)

map :: (a1 -> a2) -> (([]) a1) -> ([]) a2
map f l =
  case l of {
   ([]) -> ([]);
   (:) a t -> (:) (f a) (map f t)}

fold_left :: (a1 -> a2 -> a1) -> (([]) a2) -> a1 -> a1
fold_left f l a0 =
  case l of {
   ([]) -> a0;
   (:) b t -> fold_left f t (f a0 b)}

seq :: Prelude.Integer -> Prelude.Integer -> ([]) Prelude.Integer
seq start len =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    ([]))
    (\len0 -> (:) start
    (seq (Prelude.succ start) len0))
    len

data N =
   N0
 | Npos Prelude.Integer

z_rect :: a1 -> (Prelude.Integer -> a1) -> (Prelude.Integer -> a1) ->
          Prelude.Integer -> a1
z_rect f f0 f1 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    f)
    (\x0 ->
    f0 x0)
    (\x0 ->
    f1 x0)
    z

z_rec :: a1 -> (Prelude.Integer -> a1) -> (Prelude.Integer -> a1) ->
         Prelude.Integer -> a1
z_rec =
  z_rect

add_carry :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add_carry x0 y0 =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x)
      (add_carry p q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1)
      ((Prelude.succ) p))
      y0)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x)
      (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      ((Prelude.+) p q))
      (\_ -> (\x -> 2 Prelude.* x)
      ((Prelude.succ) p))
      y0)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      ((Prelude.succ) q))
      (\q -> (\x -> 2 Prelude.* x)
      ((Prelude.succ) q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1)
      1)
      y0)
    x0

pred_double :: Prelude.Integer -> Prelude.Integer
pred_double x0 =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
    p))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1)
    (pred_double p))
    (\_ ->
    1)
    x0

data Mask =
   IsNul
 | IsPos Prelude.Integer
 | IsNeg

succ_double_mask :: Mask -> Mask
succ_double_mask x0 =
  case x0 of {
   IsNul -> IsPos 1;
   IsPos p -> IsPos ((\x -> 2 Prelude.* x Prelude.+ 1) p);
   IsNeg -> IsNeg}

double_mask :: Mask -> Mask
double_mask x0 =
  case x0 of {
   IsPos p -> IsPos ((\x -> 2 Prelude.* x) p);
   x1 -> x1}

double_pred_mask :: Prelude.Integer -> Mask
double_pred_mask x0 =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> IsPos ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
    p)))
    (\p -> IsPos ((\x -> 2 Prelude.* x)
    (pred_double p)))
    (\_ ->
    IsNul)
    x0

sub_mask :: Prelude.Integer -> Prelude.Integer -> Mask
sub_mask x0 y0 =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q ->
      double_mask (sub_mask p q))
      (\q ->
      succ_double_mask (sub_mask p q))
      (\_ -> IsPos ((\x -> 2 Prelude.* x)
      p))
      y0)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q ->
      succ_double_mask (sub_mask_carry p q))
      (\q ->
      double_mask (sub_mask p q))
      (\_ -> IsPos
      (pred_double p))
      y0)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\_ ->
      IsNeg)
      (\_ ->
      IsNeg)
      (\_ ->
      IsNul)
      y0)
    x0

sub_mask_carry :: Prelude.Integer -> Prelude.Integer -> Mask
sub_mask_carry x0 y0 =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q ->
      succ_double_mask (sub_mask_carry p q))
      (\q ->
      double_mask (sub_mask p q))
      (\_ -> IsPos
      (pred_double p))
      y0)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q ->
      double_mask (sub_mask_carry p q))
      (\q ->
      succ_double_mask (sub_mask_carry p q))
      (\_ ->
      double_pred_mask p)
      y0)
    (\_ ->
    IsNeg)
    x0

size_nat :: Prelude.Integer -> Prelude.Integer
size_nat p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 -> Prelude.succ
    (size_nat p0))
    (\p0 -> Prelude.succ
    (size_nat p0))
    (\_ -> Prelude.succ
    0)
    p

compare_cont :: Prelude.Ordering -> Prelude.Integer -> Prelude.Integer ->
                Prelude.Ordering
compare_cont = (posCompareContAbstract43820948120402312)

ggcdn :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer -> (,)
         Prelude.Integer ((,) Prelude.Integer Prelude.Integer)
ggcdn n a b =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> (,) 1 ((,) a
    b))
    (\n0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\a' ->
      (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
        (\b' ->
        case (Prelude.compare) a' b' of {
         Prelude.EQ -> (,) a ((,) 1 1);
         Prelude.LT ->
          case ggcdn n0 ((Prelude.-) b' a') a of {
           (,) g p ->
            case p of {
             (,) ba aa -> (,) g ((,) aa
              ((Prelude.+) aa ((\x -> 2 Prelude.* x) ba)))}};
         Prelude.GT ->
          case ggcdn n0 ((Prelude.-) a' b') b of {
           (,) g p ->
            case p of {
             (,) ab bb -> (,) g ((,)
              ((Prelude.+) bb ((\x -> 2 Prelude.* x) ab)) bb)}}})
        (\b0 ->
        case ggcdn n0 a b0 of {
         (,) g p ->
          case p of {
           (,) aa bb -> (,) g ((,) aa ((\x -> 2 Prelude.* x) bb))}})
        (\_ -> (,) 1 ((,) a
        1))
        b)
      (\a0 ->
      (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
        (\_ ->
        case ggcdn n0 a0 b of {
         (,) g p ->
          case p of {
           (,) aa bb -> (,) g ((,) ((\x -> 2 Prelude.* x) aa) bb)}})
        (\b0 ->
        case ggcdn n0 a0 b0 of {
         (,) g p -> (,) ((\x -> 2 Prelude.* x) g) p})
        (\_ -> (,) 1 ((,) a
        1))
        b)
      (\_ -> (,) 1 ((,) 1
      b))
      a)
    n

ggcd :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
        ((,) Prelude.Integer Prelude.Integer)
ggcd a b =
  ggcdn ((Prelude.+) (size_nat a) (size_nat b)) a b

iter_op :: (a1 -> a1 -> a1) -> Prelude.Integer -> a1 -> a1
iter_op op p a =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 ->
    op a (iter_op op p0 (op a a)))
    (\p0 ->
    iter_op op p0 (op a a))
    (\_ ->
    a)
    p

to_nat :: Prelude.Integer -> Prelude.Integer
to_nat x0 =
  iter_op (Prelude.+) x0 (Prelude.succ 0)

of_succ_nat :: Prelude.Integer -> Prelude.Integer
of_succ_nat n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    1)
    (\x0 ->
    (Prelude.succ) (of_succ_nat x0))
    n

eq_dec :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eq_dec = (Prelude.==)

switch_Eq :: Prelude.Ordering -> Prelude.Ordering -> Prelude.Ordering
switch_Eq c c' =
  case c' of {
   Prelude.EQ -> c;
   x0 -> x0}

of_nat :: Prelude.Integer -> N
of_nat n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    N0)
    (\n' -> Npos
    (of_succ_nat n'))
    n

double :: Prelude.Integer -> Prelude.Integer
double x0 =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    0)
    (\p -> (\x -> x) ((\x -> 2 Prelude.* x)
    p))
    (\p -> Prelude.negate ((\x -> 2 Prelude.* x)
    p))
    x0

succ_double :: Prelude.Integer -> Prelude.Integer
succ_double x0 =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (\x -> x)
    1)
    (\p -> (\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
    p))
    (\p -> Prelude.negate
    (pred_double p))
    x0

pred_double0 :: Prelude.Integer -> Prelude.Integer
pred_double0 x0 =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> Prelude.negate
    1)
    (\p -> (\x -> x)
    (pred_double p))
    (\p -> Prelude.negate ((\x -> 2 Prelude.* x Prelude.+ 1)
    p))
    x0

pos_sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pos_sub x0 y0 =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q ->
      double (pos_sub p q))
      (\q ->
      succ_double (pos_sub p q))
      (\_ -> (\x -> x) ((\x -> 2 Prelude.* x)
      p))
      y0)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q ->
      pred_double0 (pos_sub p q))
      (\q ->
      double (pos_sub p q))
      (\_ -> (\x -> x)
      (pred_double p))
      y0)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> Prelude.negate ((\x -> 2 Prelude.* x)
      q))
      (\q -> Prelude.negate
      (pred_double q))
      (\_ ->
      0)
      y0)
    x0

opp :: Prelude.Integer -> Prelude.Integer
opp x0 =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    0)
    (\x1 -> Prelude.negate
    x1)
    (\x1 -> (\x -> x)
    x1)
    x0

succ :: Prelude.Integer -> Prelude.Integer
succ x0 =
  (Prelude.+) x0 ((\x -> x) 1)

compare :: Prelude.Integer -> Prelude.Integer -> Prelude.Ordering
compare x0 y0 =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      Prelude.EQ)
      (\_ ->
      Prelude.LT)
      (\_ ->
      Prelude.GT)
      y0)
    (\x' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      Prelude.GT)
      (\y' ->
      (Prelude.compare) x' y')
      (\_ ->
      Prelude.GT)
      y0)
    (\x' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      Prelude.LT)
      (\_ ->
      Prelude.LT)
      (\y' ->
      compOpp ((Prelude.compare) x' y'))
      y0)
    x0

sgn :: Prelude.Integer -> Prelude.Integer
sgn z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    0)
    (\_ -> (\x -> x)
    1)
    (\_ -> Prelude.negate
    1)
    z

leb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
leb x0 y0 =
  case compare x0 y0 of {
   Prelude.GT -> Prelude.False;
   _ -> Prelude.True}

ltb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
ltb x0 y0 =
  case compare x0 y0 of {
   Prelude.LT -> Prelude.True;
   _ -> Prelude.False}

abs :: Prelude.Integer -> Prelude.Integer
abs z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    0)
    (\p -> (\x -> x)
    p)
    (\p -> (\x -> x)
    p)
    z

abs_nat :: Prelude.Integer -> Prelude.Integer
abs_nat z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    0)
    (\p ->
    to_nat p)
    (\p ->
    to_nat p)
    z

of_nat0 :: Prelude.Integer -> Prelude.Integer
of_nat0 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    0)
    (\n0 -> (\x -> x)
    (of_succ_nat n0))
    n

to_pos :: Prelude.Integer -> Prelude.Integer
to_pos z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    1)
    (\p ->
    p)
    (\_ ->
    1)
    z

pos_div_eucl :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
                Prelude.Integer
pos_div_eucl a b =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\a' ->
    case pos_div_eucl a' b of {
     (,) q r ->
      let {
       r' = (Prelude.+) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) r)
              ((\x -> x) 1)}
      in
      case ltb r' b of {
       Prelude.True -> (,)
        ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q) r';
       Prelude.False -> (,)
        ((Prelude.+) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q)
          ((\x -> x) 1)) ((Prelude.-) r' b)}})
    (\a' ->
    case pos_div_eucl a' b of {
     (,) q r ->
      let {r' = (Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) r} in
      case ltb r' b of {
       Prelude.True -> (,)
        ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q) r';
       Prelude.False -> (,)
        ((Prelude.+) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q)
          ((\x -> x) 1)) ((Prelude.-) r' b)}})
    (\_ ->
    case leb ((\x -> x) ((\x -> 2 Prelude.* x) 1)) b of {
     Prelude.True -> (,) 0 ((\x -> x) 1);
     Prelude.False -> (,) ((\x -> x) 1) 0})
    a

div_eucl :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
            Prelude.Integer
div_eucl a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (,) 0
    0)
    (\a' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> (,) 0
      0)
      (\_ ->
      pos_div_eucl a' b)
      (\b' ->
      case pos_div_eucl a' ((\x -> x) b') of {
       (,) q r ->
        (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
          (\_ -> (,) (opp q)
          0)
          (\_ -> (,) (opp ((Prelude.+) q ((\x -> x) 1)))
          ((Prelude.+) b r))
          (\_ -> (,) (opp ((Prelude.+) q ((\x -> x) 1)))
          ((Prelude.+) b r))
          r})
      b)
    (\a' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> (,) 0
      0)
      (\_ ->
      case pos_div_eucl a' b of {
       (,) q r ->
        (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
          (\_ -> (,) (opp q)
          0)
          (\_ -> (,) (opp ((Prelude.+) q ((\x -> x) 1)))
          ((Prelude.-) b r))
          (\_ -> (,) (opp ((Prelude.+) q ((\x -> x) 1)))
          ((Prelude.-) b r))
          r})
      (\b' ->
      case pos_div_eucl a' ((\x -> x) b') of {
       (,) q r -> (,) q (opp r)})
      b)
    a

div :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
div = (\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)

ggcd0 :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
         ((,) Prelude.Integer Prelude.Integer)
ggcd0 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (,) (abs b) ((,) 0
    (sgn b)))
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> (,) (abs a) ((,) (sgn a)
      0))
      (\b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) ((\x -> x) g) ((,) ((\x -> x) aa) ((\x -> x) bb))}})
      (\b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) ((\x -> x) g) ((,) ((\x -> x) aa) (Prelude.negate
          bb))}})
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> (,) (abs a) ((,) (sgn a)
      0))
      (\b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) ((\x -> x) g) ((,) (Prelude.negate aa) ((\x -> x)
          bb))}})
      (\b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) ((\x -> x) g) ((,) (Prelude.negate aa)
          (Prelude.negate bb))}})
      b)
    a

eq_dec0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eq_dec0 x0 y0 =
  z_rec (\y1 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      Prelude.True)
      (\_ ->
      Prelude.False)
      (\_ ->
      Prelude.False)
      y1) (\p y1 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      Prelude.False)
      (\p0 ->
      sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (eq_dec p p0))
      (\_ ->
      Prelude.False)
      y1) (\p y1 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      Prelude.False)
      (\_ ->
      Prelude.False)
      (\p0 ->
      sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (eq_dec p p0))
      y1) x0 y0

zcompare_rect :: Prelude.Integer -> Prelude.Integer -> (() -> a1) -> (() ->
                 a1) -> (() -> a1) -> a1
zcompare_rect n m h1 h2 h3 =
  let {c = compare n m} in
  case c of {
   Prelude.EQ -> h1 __;
   Prelude.LT -> h2 __;
   Prelude.GT -> h3 __}

zcompare_rec :: Prelude.Integer -> Prelude.Integer -> (() -> a1) -> (() ->
                a1) -> (() -> a1) -> a1
zcompare_rec n m =
  zcompare_rect n m

z_lt_dec :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
z_lt_dec x0 y0 =
  case compare x0 y0 of {
   Prelude.LT -> Prelude.True;
   _ -> Prelude.False}

z_lt_ge_dec :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
z_lt_ge_dec x0 y0 =
  z_lt_dec x0 y0

z_lt_le_dec :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
z_lt_le_dec x0 y0 =
  sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (z_lt_ge_dec x0 y0)

z_le_lt_eq_dec :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
z_le_lt_eq_dec x0 y0 =
  zcompare_rec x0 y0 (\_ -> Prelude.False) (\_ -> Prelude.True) (\_ ->
    false_rec)

not_Zeq_inf :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
not_Zeq_inf x0 y0 =
  case z_lt_ge_dec x0 y0 of {
   Prelude.True -> Prelude.True;
   Prelude.False ->
    case z_le_lt_eq_dec y0 x0 of {
     Prelude.True -> Prelude.False;
     Prelude.False -> false_rec}}

z_dec' :: Prelude.Integer -> Prelude.Integer -> Prelude.Maybe Prelude.Bool
z_dec' x0 y0 =
  case eq_dec0 x0 y0 of {
   Prelude.True -> Prelude.Nothing;
   Prelude.False -> Prelude.Just (not_Zeq_inf x0 y0)}

zeq_bool :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
zeq_bool x0 y0 =
  case compare x0 y0 of {
   Prelude.EQ -> Prelude.True;
   _ -> Prelude.False}

pow_pos :: (a1 -> a1 -> a1) -> a1 -> Prelude.Integer -> a1
pow_pos rmul x0 i =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\i0 ->
    let {p = pow_pos rmul x0 i0} in rmul x0 (rmul p p))
    (\i0 ->
    let {p = pow_pos rmul x0 i0} in rmul p p)
    (\_ ->
    x0)
    i

qnum :: (Data.Ratio.Ratio Prelude.Integer) -> Prelude.Integer
qnum q =
  (\fp qn -> fp (Data.Ratio.numerator qn) (Data.Ratio.denominator qn))
    (\qnum0 _ ->
    qnum0)
    q

qden :: (Data.Ratio.Ratio Prelude.Integer) -> Prelude.Integer
qden q =
  (\fp qn -> fp (Data.Ratio.numerator qn) (Data.Ratio.denominator qn))
    (\_ qden0 ->
    qden0)
    q

inject_Z :: Prelude.Integer -> (Data.Ratio.Ratio Prelude.Integer)
inject_Z x0 =
  (\x y -> (Data.Ratio.%) x y) x0 1

qcompare :: (Data.Ratio.Ratio Prelude.Integer) ->
            (Data.Ratio.Ratio Prelude.Integer) -> Prelude.Ordering
qcompare p q =
  compare ((Prelude.*) (qnum p) ((\x -> x) (qden q)))
    ((Prelude.*) (qnum q) ((\x -> x) (qden p)))

qeq_dec :: (Data.Ratio.Ratio Prelude.Integer) ->
           (Data.Ratio.Ratio Prelude.Integer) -> Prelude.Bool
qeq_dec x0 y0 =
  eq_dec0 ((Prelude.*) (qnum x0) ((\x -> x) (qden y0)))
    ((Prelude.*) (qnum y0) ((\x -> x) (qden x0)))

qeq_bool :: (Data.Ratio.Ratio Prelude.Integer) ->
            (Data.Ratio.Ratio Prelude.Integer) -> Prelude.Bool
qeq_bool x0 y0 =
  zeq_bool ((Prelude.*) (qnum x0) ((\x -> x) (qden y0)))
    ((Prelude.*) (qnum y0) ((\x -> x) (qden x0)))

qplus :: (Data.Ratio.Ratio Prelude.Integer) ->
         (Data.Ratio.Ratio Prelude.Integer) ->
         (Data.Ratio.Ratio Prelude.Integer)
qplus x0 y0 =
  (\x y -> (Data.Ratio.%) x y)
    ((Prelude.+) ((Prelude.*) (qnum x0) ((\x -> x) (qden y0)))
      ((Prelude.*) (qnum y0) ((\x -> x) (qden x0))))
    ((Prelude.*) (qden x0) (qden y0))

qmult :: (Data.Ratio.Ratio Prelude.Integer) ->
         (Data.Ratio.Ratio Prelude.Integer) ->
         (Data.Ratio.Ratio Prelude.Integer)
qmult x0 y0 =
  (\x y -> (Data.Ratio.%) x y) ((Prelude.*) (qnum x0) (qnum y0))
    ((Prelude.*) (qden x0) (qden y0))

qopp :: (Data.Ratio.Ratio Prelude.Integer) ->
        (Data.Ratio.Ratio Prelude.Integer)
qopp x0 =
  (\x y -> (Data.Ratio.%) x y) (opp (qnum x0)) (qden x0)

qminus :: (Data.Ratio.Ratio Prelude.Integer) ->
          (Data.Ratio.Ratio Prelude.Integer) ->
          (Data.Ratio.Ratio Prelude.Integer)
qminus x0 y0 =
  qplus x0 (qopp y0)

qinv :: (Data.Ratio.Ratio Prelude.Integer) ->
        (Data.Ratio.Ratio Prelude.Integer)
qinv x0 =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (\x y -> (Data.Ratio.%) x y) 0
    1)
    (\p -> (\x y -> (Data.Ratio.%) x y) ((\x -> x) (qden x0))
    p)
    (\p -> (\x y -> (Data.Ratio.%) x y) (Prelude.negate (qden x0))
    p)
    (qnum x0)

qdiv :: (Data.Ratio.Ratio Prelude.Integer) ->
        (Data.Ratio.Ratio Prelude.Integer) ->
        (Data.Ratio.Ratio Prelude.Integer)
qdiv x0 y0 =
  qmult x0 (qinv y0)

q_dec :: (Data.Ratio.Ratio Prelude.Integer) ->
         (Data.Ratio.Ratio Prelude.Integer) -> Prelude.Maybe Prelude.Bool
q_dec x0 y0 =
  z_dec' ((Prelude.*) (qnum x0) ((\x -> x) (qden y0)))
    ((Prelude.*) (qnum y0) ((\x -> x) (qden x0)))

qlt_le_dec :: (Data.Ratio.Ratio Prelude.Integer) ->
              (Data.Ratio.Ratio Prelude.Integer) -> Prelude.Bool
qlt_le_dec x0 y0 =
  z_lt_le_dec ((Prelude.*) (qnum x0) ((\x -> x) (qden y0)))
    ((Prelude.*) (qnum y0) ((\x -> x) (qden x0)))

qpower_positive :: (Data.Ratio.Ratio Prelude.Integer) -> Prelude.Integer ->
                   (Data.Ratio.Ratio Prelude.Integer)
qpower_positive =
  pow_pos qmult

qpower :: (Data.Ratio.Ratio Prelude.Integer) -> Prelude.Integer ->
          (Data.Ratio.Ratio Prelude.Integer)
qpower q z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (\x y -> (Data.Ratio.%) x y) ((\x -> x) 1)
    1)
    (\p ->
    qpower_positive q p)
    (\p ->
    qinv (qpower_positive q p))
    z

qred :: (Data.Ratio.Ratio Prelude.Integer) ->
        (Data.Ratio.Ratio Prelude.Integer)
qred q =
  (\fp qn -> fp (Data.Ratio.numerator qn) (Data.Ratio.denominator qn))
    (\q1 q2 ->
    case snd (ggcd0 q1 ((\x -> x) q2)) of {
     (,) r1 r2 -> (\x y -> (Data.Ratio.%) x y) r1 (to_pos r2)})
    q

qminus' :: (Data.Ratio.Ratio Prelude.Integer) ->
           (Data.Ratio.Ratio Prelude.Integer) ->
           (Data.Ratio.Ratio Prelude.Integer)
qminus' x0 y0 =
  qred (qminus x0 y0)

firstNPos :: Prelude.Integer -> ([]) Prelude.Integer
firstNPos n =
  seq (Prelude.succ 0) (sub n (Prelude.succ 0))

equiMidPoints :: Prelude.Integer -> ([]) (Data.Ratio.Ratio Prelude.Integer)
equiMidPoints d =
  map (\m -> (\x y -> (Data.Ratio.%) x y) (of_nat0 m) d)
    (firstNPos (to_nat d))

zip :: (([]) a1) -> (([]) a2) -> ([]) ((,) a1 a2)
zip a b =
  case a of {
   ([]) -> ([]);
   (:) ah au ->
    case b of {
     ([]) -> ([]);
     (:) bh bt -> (:) ((,) ah bh) (zip au bt)}}

type Csymmetric a r = a -> a -> r -> r

data Stream a =
   Cons a (Stream a)

hd :: (Stream a1) -> a1
hd x0 =
  case x0 of {
   Cons a _ -> a}

tl :: (Stream a1) -> Stream a1
tl x0 =
  case x0 of {
   Cons _ s -> s}

map0 :: (a1 -> a2) -> (Stream a1) -> Stream a2
map0 f s =
  Cons (f (hd s)) (map0 f (tl s))

zipWith :: (a1 -> a2 -> a3) -> (Stream a1) -> (Stream a2) -> Stream a3
zipWith f a b =
  Cons (f (hd a) (hd b)) (zipWith f (tl a) (tl b))

type Cast a b = a -> b

cast :: (Cast a1 a2) -> a1 -> a2
cast cast0 =
  cast0

type Plus a = a -> a -> a

plus :: (Plus a1) -> a1 -> a1 -> a1
plus plus0 =
  plus0

type Mult a = a -> a -> a

mult :: (Mult a1) -> a1 -> a1 -> a1
mult mult0 =
  mult0

type One a = a

one :: (One a1) -> a1
one one1 =
  one1

type Zero a = a

zero :: (Zero a1) -> a1
zero zero1 =
  zero1

type Negate a = a -> a

negate :: (Negate a1) -> a1 -> a1
negate negate0 =
  negate0

type Decision = Prelude.Bool

decide :: Decision -> Prelude.Bool
decide decision =
  decision

data RSetoid =
   Build_RSetoid

type St_car = Any

type Cotransitive a r = a -> a -> r -> a -> Prelude.Either r r

data Is_CSetoid a ap =
   Build_is_CSetoid (Csymmetric a ap) (Cotransitive a ap)

data CSetoid =
   MakeCSetoid RSetoid (Is_CSetoid St_car Any)

cs_crr :: CSetoid -> RSetoid
cs_crr c =
  case c of {
   MakeCSetoid cs_crr0 _ -> cs_crr0}

type Cs_ap = Any

build_CSetoid :: (Is_CSetoid a1 a2) -> CSetoid
build_CSetoid p =
  MakeCSetoid Build_RSetoid (unsafeCoerce p)

type Bin_fun_strext =
  St_car -> St_car -> St_car -> St_car -> Cs_ap -> Prelude.Either Cs_ap Cs_ap

data CSetoid_bin_fun =
   Build_CSetoid_bin_fun (St_car -> St_car -> St_car) Bin_fun_strext

csbf_fun :: CSetoid -> CSetoid -> CSetoid -> CSetoid_bin_fun -> St_car ->
            St_car -> St_car
csbf_fun _ _ _ c =
  case c of {
   Build_CSetoid_bin_fun csbf_fun0 _ -> csbf_fun0}

type CSetoid_bin_op = CSetoid_bin_fun

data CSemiGroup =
   Build_CSemiGroup CSetoid CSetoid_bin_op

csg_crr :: CSemiGroup -> CSetoid
csg_crr c =
  case c of {
   Build_CSemiGroup csg_crr0 _ -> csg_crr0}

csg_op :: CSemiGroup -> CSetoid_bin_op
csg_op c =
  case c of {
   Build_CSemiGroup _ csg_op0 -> csg_op0}

type RealNumberPi r = r

__U03c0_ :: (RealNumberPi a1) -> a1
__U03c0_ realNumberPi =
  realNumberPi

type HalfNum r = r

half_num :: (HalfNum a1) -> a1
half_num halfNum =
  halfNum

type SFmap m = () -> () -> (Any -> Any) -> m -> m

sfmap :: (SFmap a1) -> (a2 -> a3) -> a1 -> a1
sfmap sFmap h x0 =
  unsafeCoerce sFmap __ __ h x0

qfloor :: (Data.Ratio.Ratio Prelude.Integer) -> Prelude.Integer
qfloor x0 =
  (\fp qn -> fp (Data.Ratio.numerator qn) (Data.Ratio.denominator qn))
    (\n d ->
    div n ((\x -> x) d))
    x0

qceiling :: (Data.Ratio.Ratio Prelude.Integer) -> Prelude.Integer
qceiling x0 =
  opp (qfloor (qopp x0))

qabs :: (Data.Ratio.Ratio Prelude.Integer) ->
        (Data.Ratio.Ratio Prelude.Integer)
qabs x0 =
  (\fp qn -> fp (Data.Ratio.numerator qn) (Data.Ratio.denominator qn))
    (\n d -> (\x y -> (Data.Ratio.%) x y) (abs n)
    d)
    x0

qle_dec :: (Data.Ratio.Ratio Prelude.Integer) ->
           (Data.Ratio.Ratio Prelude.Integer) -> Prelude.Bool
qle_dec x0 y0 =
  let {s = qlt_le_dec y0 x0} in
  case s of {
   Prelude.True -> Prelude.False;
   Prelude.False -> Prelude.True}

ap_Q_cotransitive0 :: (Data.Ratio.Ratio Prelude.Integer) ->
                      (Data.Ratio.Ratio Prelude.Integer) ->
                      (Data.Ratio.Ratio Prelude.Integer) -> Prelude.Either 
                      () ()
ap_Q_cotransitive0 x0 _ z =
  case qeq_dec x0 z of {
   Prelude.True -> Prelude.Right __;
   Prelude.False -> Prelude.Left __}

qplus_strext0 :: (Data.Ratio.Ratio Prelude.Integer) ->
                 (Data.Ratio.Ratio Prelude.Integer) ->
                 (Data.Ratio.Ratio Prelude.Integer) ->
                 (Data.Ratio.Ratio Prelude.Integer) -> Prelude.Either 
                 Any Any
qplus_strext0 x1 x2 _ _ =
  case qeq_dec x1 x2 of {
   Prelude.True -> Prelude.Right __;
   Prelude.False -> Prelude.Left __}

ap_Q_cotransitive1 :: (Data.Ratio.Ratio Prelude.Integer) ->
                      (Data.Ratio.Ratio Prelude.Integer) ->
                      (Data.Ratio.Ratio Prelude.Integer) -> Prelude.Either 
                      () ()
ap_Q_cotransitive1 x0 y0 z =
  ap_Q_cotransitive0 x0 y0 z

ap_Q_is_apartness :: Is_CSetoid (Data.Ratio.Ratio Prelude.Integer) ()
ap_Q_is_apartness =
  Build_is_CSetoid __ (\x0 x1 _ -> ap_Q_cotransitive1 x0 x1)

q_as_CSetoid :: CSetoid
q_as_CSetoid =
  build_CSetoid ap_Q_is_apartness

q_is_Setoid :: RSetoid
q_is_Setoid =
  cs_crr q_as_CSetoid

qplus_strext1 :: St_car -> St_car -> St_car -> St_car -> Prelude.Either 
                 Cs_ap Cs_ap
qplus_strext1 x1 x2 y1 y2 =
  qplus_strext0 (unsafeCoerce x1) (unsafeCoerce x2) (unsafeCoerce y1)
    (unsafeCoerce y2)

qplus_is_bin_fun :: CSetoid_bin_fun
qplus_is_bin_fun =
  Build_CSetoid_bin_fun (unsafeCoerce qplus) (\x0 x1 x2 x3 _ ->
    qplus_strext1 x0 x1 x2 x3)

q_as_CSemiGroup :: CSemiGroup
q_as_CSemiGroup =
  Build_CSemiGroup q_as_CSetoid qplus_is_bin_fun

type Qpos = (Data.Ratio.Ratio Prelude.Integer)

qposMake :: Prelude.Integer -> Prelude.Integer -> Qpos
qposMake num den =
  (\x y -> (Data.Ratio.%) x y) ((\x -> x) num) den

qposAsQ :: Qpos -> (Data.Ratio.Ratio Prelude.Integer)
qposAsQ =
  proj1_sig

mkQpos :: (Data.Ratio.Ratio Prelude.Integer) -> Qpos
mkQpos a =
  a

qpos_mult :: Qpos -> Qpos -> Qpos
qpos_mult x0 y0 =
  qmult (qposAsQ x0) (qposAsQ y0)

qpos_inv :: Qpos -> Qpos
qpos_inv x0 =
  qinv (qposAsQ x0)

qpos_lt_plus :: (Data.Ratio.Ratio Prelude.Integer) ->
                (Data.Ratio.Ratio Prelude.Integer) -> SigT Qpos ()
qpos_lt_plus a b =
  ExistT (mkQpos (qminus b a)) __

min :: (a1 -> a1 -> Prelude.Bool) -> a1 -> a1 -> a1
min le_total x0 y0 =
  case le_total x0 y0 of {
   Prelude.True -> x0;
   Prelude.False -> y0}

max :: (a1 -> a1 -> Prelude.Bool) -> a1 -> a1 -> a1
max le_total x0 y0 =
  case le_total y0 x0 of {
   Prelude.True -> x0;
   Prelude.False -> y0}

qlt_le_dec_fast :: (Data.Ratio.Ratio Prelude.Integer) ->
                   (Data.Ratio.Ratio Prelude.Integer) -> Prelude.Bool
qlt_le_dec_fast x0 y0 =
  let {c = qcompare x0 y0} in
  case c of {
   Prelude.LT -> Prelude.True;
   _ -> Prelude.False}

qle_total :: (Data.Ratio.Ratio Prelude.Integer) ->
             (Data.Ratio.Ratio Prelude.Integer) -> Prelude.Bool
qle_total x0 y0 =
  qlt_le_dec_fast x0 y0

qmin :: (Data.Ratio.Ratio Prelude.Integer) ->
        (Data.Ratio.Ratio Prelude.Integer) ->
        (Data.Ratio.Ratio Prelude.Integer)
qmin =
  min qle_total

qmax :: (Data.Ratio.Ratio Prelude.Integer) ->
        (Data.Ratio.Ratio Prelude.Integer) ->
        (Data.Ratio.Ratio Prelude.Integer)
qmax =
  max qle_total

data QposInf =
   Qpos2QposInf Qpos
 | QposInfinity

qposInf_bind :: (Qpos -> QposInf) -> QposInf -> QposInf
qposInf_bind f x0 =
  case x0 of {
   Qpos2QposInf x' -> f x';
   QposInfinity -> QposInfinity}

qposInf_mult :: QposInf -> QposInf -> QposInf
qposInf_mult x0 y0 =
  qposInf_bind (\x' ->
    qposInf_bind (\y' -> Qpos2QposInf (qpos_mult x' y')) y0) x0

type MetricSpace =
  RSetoid
  -- singleton inductive, whose constructor was Build_MetricSpace
  
ball_ex_dec :: MetricSpace -> (Qpos -> St_car -> St_car -> Prelude.Bool) ->
               QposInf -> St_car -> St_car -> Prelude.Bool
ball_ex_dec _ ball_dec e a b =
  case e of {
   Qpos2QposInf e0 -> ball_dec e0 a b;
   QposInfinity -> Prelude.True}

data UniformlyContinuousFunction =
   Build_UniformlyContinuousFunction (St_car -> St_car) (Qpos -> QposInf)

ucFun :: MetricSpace -> MetricSpace -> UniformlyContinuousFunction -> St_car
         -> St_car
ucFun _ _ u =
  case u of {
   Build_UniformlyContinuousFunction ucFun0 _ -> ucFun0}

mu :: MetricSpace -> MetricSpace -> UniformlyContinuousFunction -> Qpos ->
      QposInf
mu _ _ u =
  case u of {
   Build_UniformlyContinuousFunction _ mu0 -> mu0}

uc_Setoid :: MetricSpace -> MetricSpace -> RSetoid
uc_Setoid _ _ =
  Build_RSetoid

uniformlyContinuousSpace :: MetricSpace -> MetricSpace -> MetricSpace
uniformlyContinuousSpace x0 y0 =
  uc_Setoid x0 y0

ucFun2 :: MetricSpace -> MetricSpace -> MetricSpace -> St_car -> St_car ->
          St_car -> St_car
ucFun2 x0 y0 z f x1 y1 =
  ucFun y0 z (unsafeCoerce ucFun x0 (uniformlyContinuousSpace y0 z) f x1) y1

uc_compose :: MetricSpace -> MetricSpace -> MetricSpace -> St_car -> St_car
              -> St_car
uc_compose x0 y0 z g f =
  unsafeCoerce (Build_UniformlyContinuousFunction (\x1 ->
    ucFun y0 z (unsafeCoerce g) (ucFun x0 y0 (unsafeCoerce f) x1)) (\e ->
    qposInf_bind (mu x0 y0 (unsafeCoerce f)) (mu y0 z (unsafeCoerce g) e)))

type DecidableMetric = Qpos -> St_car -> St_car -> Prelude.Bool

type RegularFunction =
  QposInf -> St_car
  -- singleton inductive, whose constructor was Build_RegularFunction
  
approximate :: MetricSpace -> RegularFunction -> QposInf -> St_car
approximate _ r =
  r

regFun_Setoid :: MetricSpace -> RSetoid
regFun_Setoid _ =
  Build_RSetoid

complete :: MetricSpace -> MetricSpace
complete x0 =
  regFun_Setoid x0

cunit_fun :: MetricSpace -> St_car -> St_car
cunit_fun _ x0 =
  unsafeCoerce (\_ -> x0)

cunit :: MetricSpace -> St_car
cunit x0 =
  unsafeCoerce (Build_UniformlyContinuousFunction (cunit_fun x0) (\x1 ->
    Qpos2QposInf x1))

cjoin_raw :: MetricSpace -> St_car -> QposInf -> St_car
cjoin_raw x0 x1 e =
  approximate x0
    (unsafeCoerce approximate (complete x0) x1
      (qposInf_mult (Qpos2QposInf (qposMake 1 ((\x -> 2 Prelude.* x) 1))) e))
    (qposInf_mult (Qpos2QposInf (qposMake 1 ((\x -> 2 Prelude.* x) 1))) e)

cjoin_fun :: MetricSpace -> St_car -> St_car
cjoin_fun x0 x1 =
  unsafeCoerce cjoin_raw x0 x1

cjoin :: MetricSpace -> St_car
cjoin x0 =
  unsafeCoerce (Build_UniformlyContinuousFunction (cjoin_fun x0) (\x1 ->
    Qpos2QposInf x1))

cmap_fun :: MetricSpace -> MetricSpace -> St_car -> St_car -> St_car
cmap_fun x0 y0 f x1 =
  unsafeCoerce (\e ->
    ucFun x0 y0 (unsafeCoerce f)
      (approximate x0 (unsafeCoerce x1)
        (qposInf_bind (mu x0 y0 (unsafeCoerce f)) e)))

cmap :: MetricSpace -> MetricSpace -> St_car -> St_car
cmap x0 y0 f =
  unsafeCoerce (Build_UniformlyContinuousFunction (cmap_fun x0 y0 f)
    (mu x0 y0 (unsafeCoerce f)))

cbind :: MetricSpace -> MetricSpace -> St_car -> St_car
cbind x0 y0 f =
  uc_compose (complete x0) (complete (complete y0)) (complete y0) (cjoin y0)
    (cmap x0 (complete y0) f)

cap_raw :: MetricSpace -> MetricSpace -> St_car -> St_car -> QposInf ->
           St_car
cap_raw x0 y0 f x1 e =
  approximate y0
    (unsafeCoerce ucFun (complete x0) (complete y0)
      (cmap x0 y0
        (approximate (uniformlyContinuousSpace x0 y0) (unsafeCoerce f)
          (qposInf_mult (Qpos2QposInf (qposMake 1 ((\x -> 2 Prelude.* x) 1)))
            e))) x1)
    (qposInf_mult (Qpos2QposInf (qposMake 1 ((\x -> 2 Prelude.* x) 1))) e)

cap_fun :: MetricSpace -> MetricSpace -> St_car -> St_car -> St_car
cap_fun x0 y0 f x1 =
  unsafeCoerce cap_raw x0 y0 f x1

cap_modulus :: MetricSpace -> MetricSpace -> St_car -> Qpos -> QposInf
cap_modulus x0 y0 f e =
  mu x0 y0
    (unsafeCoerce approximate (uniformlyContinuousSpace x0 y0) f
      (Qpos2QposInf
      (qpos_mult (qposMake 1 ((\x -> 2 Prelude.* x Prelude.+ 1) 1)) e)))
    (qpos_mult (qposMake 1 ((\x -> 2 Prelude.* x Prelude.+ 1) 1)) e)

cap_weak :: MetricSpace -> MetricSpace -> St_car -> St_car
cap_weak x0 y0 f =
  unsafeCoerce (Build_UniformlyContinuousFunction (cap_fun x0 y0 f)
    (cap_modulus x0 y0 f))

cap :: MetricSpace -> MetricSpace -> St_car
cap x0 y0 =
  unsafeCoerce (Build_UniformlyContinuousFunction (cap_weak x0 y0) (\x1 ->
    Qpos2QposInf x1))

cmap2 :: MetricSpace -> MetricSpace -> MetricSpace -> St_car -> St_car
cmap2 x0 y0 z f =
  uc_compose (complete x0) (complete (uniformlyContinuousSpace y0 z))
    (uniformlyContinuousSpace (complete y0) (complete z)) (cap y0 z)
    (cmap x0 (uniformlyContinuousSpace y0 z) f)

q_as_MetricSpace :: MetricSpace
q_as_MetricSpace =
  q_is_Setoid

qmetric_dec :: DecidableMetric
qmetric_dec e a b =
  let {c = qopp (qposAsQ e)} in
  let {d = qminus (unsafeCoerce a) (unsafeCoerce b)} in
  let {s = qlt_le_dec_fast d c} in
  case s of {
   Prelude.True -> Prelude.False;
   Prelude.False ->
    let {s0 = qlt_le_dec_fast (qposAsQ e) d} in
    case s0 of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True}}

qball_ex_bool :: QposInf -> St_car -> St_car -> Prelude.Bool
qball_ex_bool e a b =
  case ball_ex_dec q_as_MetricSpace qmetric_dec e a b of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

z_plus :: Plus Prelude.Integer
z_plus =
  (Prelude.+)

z_0 :: Zero Prelude.Integer
z_0 =
  0

z_1 :: One Prelude.Integer
z_1 =
  (\x -> x) 1

z_mult :: Mult Prelude.Integer
z_mult =
  (Prelude.*)

z_negate :: Negate Prelude.Integer
z_negate =
  opp

q_0 :: Zero (Data.Ratio.Ratio Prelude.Integer)
q_0 =
  (\x y -> (Data.Ratio.%) x y) 0 1

q_1 :: One (Data.Ratio.Ratio Prelude.Integer)
q_1 =
  (\x y -> (Data.Ratio.%) x y) ((\x -> x) 1) 1

q_opp :: Negate (Data.Ratio.Ratio Prelude.Integer)
q_opp =
  qopp

q_plus :: Plus (Data.Ratio.Ratio Prelude.Integer)
q_plus =
  qplus

q_mult :: Mult (Data.Ratio.Ratio Prelude.Integer)
q_mult =
  qmult

inject_Z_Q :: Cast Prelude.Integer (Data.Ratio.Ratio Prelude.Integer)
inject_Z_Q =
  inject_Z

decision_instance_1 :: (Data.Ratio.Ratio Prelude.Integer) ->
                       (Data.Ratio.Ratio Prelude.Integer) -> Decision
decision_instance_1 y0 x0 =
  let {filtered_var = qlt_le_dec x0 y0} in
  case filtered_var of {
   Prelude.True -> Prelude.False;
   Prelude.False -> Prelude.True}

cR :: MetricSpace
cR =
  complete q_as_MetricSpace

inject_Q_CR :: Cast (Data.Ratio.Ratio Prelude.Integer) St_car
inject_Q_CR =
  unsafeCoerce ucFun q_as_MetricSpace (complete q_as_MetricSpace)
    (cunit q_as_MetricSpace)

cR0 :: Zero St_car
cR0 =
  cast inject_Q_CR ((\x y -> (Data.Ratio.%) x y) 0 1)

cR1 :: One St_car
cR1 =
  cast inject_Q_CR ((\x y -> (Data.Ratio.%) x y) ((\x -> x) 1) 1)

qtranslate_uc :: St_car -> St_car
qtranslate_uc a =
  unsafeCoerce (Build_UniformlyContinuousFunction (\b ->
    csbf_fun (csg_crr q_as_CSemiGroup) (csg_crr q_as_CSemiGroup)
      (csg_crr q_as_CSemiGroup) (csg_op q_as_CSemiGroup) a b) (\x0 ->
    Qpos2QposInf x0))

qplus_uc :: St_car
qplus_uc =
  unsafeCoerce (Build_UniformlyContinuousFunction qtranslate_uc (\x0 ->
    Qpos2QposInf x0))

cRplus_uc :: St_car
cRplus_uc =
  cmap2 q_as_MetricSpace q_as_MetricSpace q_as_MetricSpace qplus_uc

cRplus :: Plus St_car
cRplus =
  ucFun2 cR cR cR cRplus_uc

qopp_uc :: St_car
qopp_uc =
  unsafeCoerce (Build_UniformlyContinuousFunction (unsafeCoerce qopp) (\x0 ->
    Qpos2QposInf x0))

cRopp :: Negate St_car
cRopp =
  ucFun (complete q_as_MetricSpace) (complete q_as_MetricSpace)
    (unsafeCoerce cmap q_as_MetricSpace q_as_MetricSpace qopp_uc)

qboundBelow_uc :: St_car -> St_car
qboundBelow_uc a =
  unsafeCoerce (Build_UniformlyContinuousFunction (\b ->
    unsafeCoerce qmax a b) (\x0 -> Qpos2QposInf x0))

qboundAbove_uc :: St_car -> St_car
qboundAbove_uc a =
  unsafeCoerce (Build_UniformlyContinuousFunction (\b ->
    unsafeCoerce qmin a b) (\x0 -> Qpos2QposInf x0))

type CRpos = Qpos

type CRltT = CRpos

type CRapartT = Prelude.Either CRltT CRltT

qscale_modulus :: (Data.Ratio.Ratio Prelude.Integer) -> Qpos -> QposInf
qscale_modulus a e =
  (\fp qn -> fp (Data.Ratio.numerator qn) (Data.Ratio.denominator qn))
    (\qnum0 ad ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ ->
      QposInfinity)
      (\an -> Qpos2QposInf
      (qpos_mult (qposMake ad an) e))
      (\an -> Qpos2QposInf
      (qpos_mult (qposMake ad an) e))
      qnum0)
    a

qscale_uc :: St_car -> St_car
qscale_uc a =
  unsafeCoerce (Build_UniformlyContinuousFunction (\b ->
    unsafeCoerce qmult a b) (qscale_modulus (unsafeCoerce a)))

scale :: (Data.Ratio.Ratio Prelude.Integer) -> St_car
scale a =
  cmap q_as_MetricSpace q_as_MetricSpace (qscale_uc (unsafeCoerce a))

qboundAbs :: Qpos -> St_car
qboundAbs c =
  uc_compose q_as_MetricSpace q_as_MetricSpace q_as_MetricSpace
    (qboundBelow_uc (unsafeCoerce qopp (qposAsQ c)))
    (qboundAbove_uc (unsafeCoerce qposAsQ c))

qmult_modulus :: Qpos -> Qpos -> QposInf
qmult_modulus c e =
  Qpos2QposInf (qpos_mult e (qpos_inv c))

qmult_uc :: Qpos -> St_car
qmult_uc c =
  unsafeCoerce (Build_UniformlyContinuousFunction (\a ->
    uc_compose q_as_MetricSpace q_as_MetricSpace q_as_MetricSpace
      (qscale_uc a) (qboundAbs c)) (qmult_modulus c))

cRmult_bounded :: Qpos -> St_car
cRmult_bounded c =
  cmap2 q_as_MetricSpace q_as_MetricSpace q_as_MetricSpace (qmult_uc c)

cR_b :: Qpos -> St_car -> Qpos
cR_b e x0 =
  mkQpos
    (qplus
      (qabs (unsafeCoerce approximate q_as_MetricSpace x0 (Qpos2QposInf e)))
      (qposAsQ e))

cRmult :: Mult St_car
cRmult x0 y0 =
  ucFun2 cR cR cR (cRmult_bounded (cR_b (qposMake 1 1) y0)) x0 y0

qinv_modulus :: Qpos -> Qpos -> Qpos
qinv_modulus c e =
  qpos_mult (qpos_mult c c) e

qinv_pos_uc :: Qpos -> St_car
qinv_pos_uc c =
  unsafeCoerce (Build_UniformlyContinuousFunction (\a ->
    unsafeCoerce qinv (qmax (qposAsQ c) (unsafeCoerce a))) (\e ->
    Qpos2QposInf (qinv_modulus c e)))

cRinv_pos :: Qpos -> St_car
cRinv_pos c =
  cmap q_as_MetricSpace q_as_MetricSpace (qinv_pos_uc c)

cRinvT :: St_car -> CRapartT -> St_car
cRinvT x0 x_ =
  case x_ of {
   Prelude.Left c0 ->
    cRopp (ucFun cR cR (unsafeCoerce cRinv_pos c0) (cRopp x0));
   Prelude.Right c0 -> ucFun cR cR (unsafeCoerce cRinv_pos c0) x0}

data Cart2D t =
   MkCart2D t t

x :: (Cart2D a1) -> a1
x c =
  case c of {
   MkCart2D x0 _ -> x0}

y :: (Cart2D a1) -> a1
y c =
  case c of {
   MkCart2D _ y0 -> y0}

zero_instance_Cart2D :: (Zero a1) -> Zero (Cart2D a1)
zero_instance_Cart2D h =
  MkCart2D (zero h) (zero h)

plus_instance_Cart2D :: (Plus a1) -> Plus (Cart2D a1)
plus_instance_Cart2D h a b =
  MkCart2D (plus h (x a) (x b)) (plus h (y a) (y b))

mutt_instance_Cart2D :: (Mult a1) -> Mult (Cart2D a1)
mutt_instance_Cart2D h a b =
  MkCart2D (mult h (x a) (x b)) (mult h (y a) (y b))

negate_instance_Cart2D :: (Negate a1) -> Negate (Cart2D a1)
negate_instance_Cart2D h a =
  MkCart2D (negate h (x a)) (negate h (y a))

sameXY :: a1 -> Cart2D a1
sameXY a =
  MkCart2D a a

castCRCart2DCR :: Cast a1 (Cart2D a1)
castCRCart2DCR =
  sameXY

qap_CRap :: (Data.Ratio.Ratio Prelude.Integer) ->
            (Data.Ratio.Ratio Prelude.Integer) -> CRapartT
qap_CRap x0 y0 =
  let {s = q_dec x0 y0} in
  case s of {
   Prelude.Just s0 ->
    case s0 of {
     Prelude.True ->
      let {s1 = qpos_lt_plus x0 y0} in
      case s1 of {
       ExistT c _ -> Prelude.Left c};
     Prelude.False ->
      let {s1 = qpos_lt_plus y0 x0} in
      case s1 of {
       ExistT c _ -> Prelude.Right c}};
   Prelude.Nothing -> false_rec}

cR_epsilon_sign_dec :: Qpos -> St_car -> Prelude.Ordering
cR_epsilon_sign_dec e x0 =
  let {z = approximate q_as_MetricSpace (unsafeCoerce x0) (Qpos2QposInf e)}
  in
  case qle_dec
         (qmult ((\x y -> (Data.Ratio.%) x y) ((\x -> x)
           ((\x -> 2 Prelude.* x) 1)) 1) (qposAsQ e)) (unsafeCoerce z) of {
   Prelude.True -> Prelude.GT;
   Prelude.False ->
    case qle_dec (unsafeCoerce z)
           (qmult
             (qopp ((\x y -> (Data.Ratio.%) x y) ((\x -> x)
               ((\x -> 2 Prelude.* x) 1)) 1)) (qposAsQ e)) of {
     Prelude.True -> Prelude.LT;
     Prelude.False -> Prelude.EQ}}

approximateQ :: (Data.Ratio.Ratio Prelude.Integer) -> Prelude.Integer ->
                (Data.Ratio.Ratio Prelude.Integer)
approximateQ x0 p =
  (\fp qn -> fp (Data.Ratio.numerator qn) (Data.Ratio.denominator qn))
    (\n d -> (\x y -> (Data.Ratio.%) x y)
    (div ((Prelude.*) n ((\x -> x) p)) ((\x -> x) d))
    p)
    x0

compress_raw :: St_car -> QposInf -> (Data.Ratio.Ratio Prelude.Integer)
compress_raw x0 e =
  case e of {
   Qpos2QposInf e0 ->
    (\fp qn -> fp (Data.Ratio.numerator qn) (Data.Ratio.denominator qn))
      (\n d ->
      (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
        (\_ ->
        unsafeCoerce approximate q_as_MetricSpace x0 (Qpos2QposInf e0))
        (\p ->
        approximateQ
          (unsafeCoerce approximate q_as_MetricSpace x0 (Qpos2QposInf
            (qposMake 1 p))) p)
        (\_ ->
        unsafeCoerce approximate q_as_MetricSpace x0 (Qpos2QposInf e0))
        (succ
          (div
            ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) ((\x -> x) d))
            n)))
      (qposAsQ e0);
   QposInfinity -> unsafeCoerce approximate q_as_MetricSpace x0 e}

compress_fun :: St_car -> St_car
compress_fun x0 =
  unsafeCoerce compress_raw x0

compress :: St_car
compress =
  unsafeCoerce (Build_UniformlyContinuousFunction compress_fun (\x0 ->
    Qpos2QposInf x0))

iterate :: (a1 -> a1) -> a1 -> Stream a1
iterate f x0 =
  Cons x0 (iterate f (f x0))

takeUntil :: ((Stream a1) -> Prelude.Bool) -> (Stream a1) -> (a1 -> a2 -> a2)
             -> a2 -> a2
takeUntil p s cons nil =
  case p s of {
   Prelude.True -> nil;
   Prelude.False -> cons (hd s) (takeUntil p (tl s) cons nil)}

everyOther :: (Stream a1) -> Stream a1
everyOther s =
  Cons (hd s) (everyOther (tl (tl s)))

mult_Streams :: (Mult a1) -> (Stream a1) -> (Stream a1) -> Stream a1
mult_Streams h1 =
  zipWith (mult h1)

powers_help :: (Mult a1) -> a1 -> a1 -> Stream a1
powers_help h1 a =
  iterate (\y0 -> mult h1 y0 a)

partialAlternatingSumUntil :: ((Stream (Data.Ratio.Ratio Prelude.Integer)) ->
                              Prelude.Bool) -> (Stream
                              (Data.Ratio.Ratio Prelude.Integer)) ->
                              (Data.Ratio.Ratio Prelude.Integer)
partialAlternatingSumUntil p s =
  takeUntil p s qminus' (zero q_0)

infiniteAlternatingSum_raw :: (Stream (Data.Ratio.Ratio Prelude.Integer)) ->
                              QposInf -> (Data.Ratio.Ratio Prelude.Integer)
infiniteAlternatingSum_raw s __U03b5_ =
  partialAlternatingSumUntil (\s0 ->
    qball_ex_bool __U03b5_ (hd (unsafeCoerce s0))
      (unsafeCoerce ((\x y -> (Data.Ratio.%) x y) 0 1))) s

infiniteAlternatingSum :: (Stream (Data.Ratio.Ratio Prelude.Integer)) ->
                          St_car
infiniteAlternatingSum seq0 =
  unsafeCoerce infiniteAlternatingSum_raw seq0

ppositives_help :: Prelude.Integer -> Stream Prelude.Integer
ppositives_help n =
  Cons n (ppositives_help ((Prelude.succ) n))

ppositives :: Stream Prelude.Integer
ppositives =
  ppositives_help 1

qrecip_positives :: Stream (Data.Ratio.Ratio Prelude.Integer)
qrecip_positives =
  map0 (\x0 -> (\x y -> (Data.Ratio.%) x y) ((\x -> x) 1) x0) ppositives

pfactorials_help :: Prelude.Integer -> Prelude.Integer -> Stream
                    Prelude.Integer
pfactorials_help n c =
  Cons c (pfactorials_help ((Prelude.succ) n) ((Prelude.*) n c))

pfactorials :: Stream Prelude.Integer
pfactorials =
  pfactorials_help 1 1

qrecip_factorials :: Stream (Data.Ratio.Ratio Prelude.Integer)
qrecip_factorials =
  map0 (\x0 -> (\x y -> (Data.Ratio.%) x y) ((\x -> x) 1) x0) pfactorials

arctanSequence :: (Data.Ratio.Ratio Prelude.Integer) -> Stream
                  (Data.Ratio.Ratio Prelude.Integer)
arctanSequence a =
  mult_Streams q_mult (everyOther qrecip_positives)
    (powers_help q_mult (qpower a ((\x -> x) ((\x -> 2 Prelude.* x) 1))) a)

rational_arctan_small_pos :: (Data.Ratio.Ratio Prelude.Integer) -> St_car
rational_arctan_small_pos a =
  infiniteAlternatingSum (arctanSequence a)

r_pi :: (Data.Ratio.Ratio Prelude.Integer) -> St_car
r_pi r =
  ucFun2 cR cR cR cRplus_uc
    (ucFun2 cR cR cR cRplus_uc
      (ucFun cR cR
        (unsafeCoerce scale
          (qmult
            (inject_Z ((\x -> x) ((\x -> 2 Prelude.* x)
              ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
              ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
              ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
              1))))))))) r))
        (rational_arctan_small_pos ((\x y -> (Data.Ratio.%) x y) ((\x -> x)
          1) ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
          ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
          ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))
      (ucFun cR cR
        (unsafeCoerce scale
          (qmult
            (inject_Z ((\x -> x) ((\x -> 2 Prelude.* x)
              ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
              ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))) r))
        (rational_arctan_small_pos ((\x y -> (Data.Ratio.%) x y) ((\x -> x)
          1) ((\x -> 2 Prelude.* x Prelude.+ 1)
          ((\x -> 2 Prelude.* x Prelude.+ 1)
          ((\x -> 2 Prelude.* x Prelude.+ 1)
          ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
          ((\x -> 2 Prelude.* x Prelude.+ 1)
          ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))))))
    (ucFun2 cR cR cR cRplus_uc
      (ucFun cR cR
        (unsafeCoerce scale
          (qmult
            (qopp
              (inject_Z ((\x -> x) ((\x -> 2 Prelude.* x)
                ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
                ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
                1)))))))) r))
        (rational_arctan_small_pos ((\x y -> (Data.Ratio.%) x y) ((\x -> x)
          1) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
          ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
          ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
          ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
          ((\x -> 2 Prelude.* x) 1))))))))))))
      (ucFun cR cR
        (unsafeCoerce scale
          (qmult
            (inject_Z ((\x -> x) ((\x -> 2 Prelude.* x)
              ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
              ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
              ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))))) r))
        (rational_arctan_small_pos ((\x y -> (Data.Ratio.%) x y) ((\x -> x)
          1) ((\x -> 2 Prelude.* x Prelude.+ 1)
          ((\x -> 2 Prelude.* x Prelude.+ 1)
          ((\x -> 2 Prelude.* x Prelude.+ 1)
          ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
          ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
          ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
          ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
          ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
          1)))))))))))))))))

cRpi :: St_car
cRpi =
  r_pi ((\x y -> (Data.Ratio.%) x y) ((\x -> x) 1) 1)

sinSequence :: (Data.Ratio.Ratio Prelude.Integer) -> Stream
               (Data.Ratio.Ratio Prelude.Integer)
sinSequence a =
  mult_Streams q_mult (everyOther (tl qrecip_factorials))
    (powers_help q_mult (qpower a ((\x -> x) ((\x -> 2 Prelude.* x) 1))) a)

rational_sin_small_pos :: (Data.Ratio.Ratio Prelude.Integer) -> St_car
rational_sin_small_pos a =
  infiniteAlternatingSum (sinSequence a)

sin_poly_fun :: (Data.Ratio.Ratio Prelude.Integer) ->
                (Data.Ratio.Ratio Prelude.Integer)
sin_poly_fun x0 =
  qmult x0
    (qminus (plus q_plus (one q_1) (plus q_plus (one q_1) (one q_1)))
      (qmult
        (qmult
          (plus q_plus (one q_1)
            (plus q_plus (one q_1) (plus q_plus (one q_1) (one q_1)))) x0)
        x0))

sin_poly_modulus :: Qpos -> QposInf
sin_poly_modulus e =
  Qpos2QposInf
    (qpos_mult
      (qposMake 1 ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
        ((\x -> 2 Prelude.* x) 1)))) e)

sin_poly_uc :: St_car
sin_poly_uc =
  unsafeCoerce (Build_UniformlyContinuousFunction (\x0 ->
    unsafeCoerce sin_poly_fun
      (ucFun q_as_MetricSpace q_as_MetricSpace
        (unsafeCoerce qboundAbs (qposMake 1 1)) x0)) sin_poly_modulus)

sin_poly :: St_car
sin_poly =
  uc_compose (complete q_as_MetricSpace) cR cR compress
    (cmap q_as_MetricSpace q_as_MetricSpace sin_poly_uc)

rational_sin_pos_bounded :: Prelude.Integer ->
                            (Data.Ratio.Ratio Prelude.Integer) -> St_car
rational_sin_pos_bounded n a =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    rational_sin_small_pos a)
    (\n' ->
    case qlt_le_dec_fast ((\x y -> (Data.Ratio.%) x y) ((\x -> x) 1) 1) a of {
     Prelude.True ->
      ucFun cR cR (unsafeCoerce sin_poly)
        (rational_sin_pos_bounded n'
          (qdiv a (plus q_plus (one q_1) (plus q_plus (one q_1) (one q_1)))));
     Prelude.False -> rational_sin_small_pos a})
    n

rational_sin_pos :: (Data.Ratio.Ratio Prelude.Integer) -> St_car
rational_sin_pos a =
  rational_sin_pos_bounded
    ((\fp qn -> fp (Data.Ratio.numerator qn) (Data.Ratio.denominator qn))
       (\n _ ->
       (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
         (\_ ->
         0)
         (\p ->
         size_nat p)
         (\_ ->
         0)
         n)
       a) a

rational_sin :: (Data.Ratio.Ratio Prelude.Integer) -> St_car
rational_sin a =
  case qle_total ((\x y -> (Data.Ratio.%) x y) 0 1) a of {
   Prelude.True -> rational_sin_pos a;
   Prelude.False -> cRopp (rational_sin_pos (qopp a))}

sin_uc :: St_car
sin_uc =
  unsafeCoerce (Build_UniformlyContinuousFunction (unsafeCoerce rational_sin)
    (\x0 -> Qpos2QposInf x0))

sin_slow :: St_car
sin_slow =
  cbind q_as_MetricSpace q_as_MetricSpace sin_uc

sin :: St_car -> St_car
sin x0 =
  ucFun cR cR (unsafeCoerce sin_slow)
    (ucFun2 cR cR cR cRplus_uc x0
      (cRopp
        (ucFun cR cR (unsafeCoerce compress)
          (ucFun cR cR
            (unsafeCoerce scale
              (qmult (plus q_plus (one q_1) (one q_1))
                (inject_Z
                  (qceiling
                    (qminus
                      (unsafeCoerce approximate q_as_MetricSpace
                        (cRmult x0
                          (ucFun cR cR
                            (unsafeCoerce cRinv_pos
                              (qposMake ((\x -> 2 Prelude.* x)
                                ((\x -> 2 Prelude.* x Prelude.+ 1) 1)) 1))
                            (ucFun cR cR
                              (unsafeCoerce scale
                                (plus q_plus (one q_1) (one q_1))) cRpi)))
                        (Qpos2QposInf
                        (qposMake 1 ((\x -> 2 Prelude.* x) 1))))
                      ((\x y -> (Data.Ratio.%) x y) ((\x -> x) 1)
                      ((\x -> 2 Prelude.* x) 1))))))) cRpi))))

cos_poly_fun :: (Data.Ratio.Ratio Prelude.Integer) ->
                (Data.Ratio.Ratio Prelude.Integer)
cos_poly_fun x0 =
  qminus ((\x y -> (Data.Ratio.%) x y) ((\x -> x) 1) 1)
    (qmult
      (qmult ((\x y -> (Data.Ratio.%) x y) ((\x -> x) ((\x -> 2 Prelude.* x)
        1)) 1) x0) x0)

cos_poly_modulus :: Qpos -> QposInf
cos_poly_modulus e =
  Qpos2QposInf
    (qpos_mult (qposMake 1 ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))
      e)

cos_poly_uc :: St_car
cos_poly_uc =
  unsafeCoerce (Build_UniformlyContinuousFunction (\x0 ->
    unsafeCoerce cos_poly_fun
      (ucFun q_as_MetricSpace q_as_MetricSpace
        (unsafeCoerce qboundAbs (qposMake 1 1)) x0)) cos_poly_modulus)

cos_poly :: St_car
cos_poly =
  cmap q_as_MetricSpace q_as_MetricSpace cos_poly_uc

rational_cos :: (Data.Ratio.Ratio Prelude.Integer) -> St_car
rational_cos x0 =
  ucFun cR cR (unsafeCoerce cos_poly)
    (rational_sin (qdiv x0 (plus q_plus (one q_1) (one q_1))))

cos_uc :: St_car
cos_uc =
  unsafeCoerce (Build_UniformlyContinuousFunction (unsafeCoerce rational_cos)
    (\x0 -> Qpos2QposInf x0))

cos_slow :: St_car
cos_slow =
  cbind q_as_MetricSpace q_as_MetricSpace cos_uc

cos :: St_car -> St_car
cos x0 =
  ucFun cR cR (unsafeCoerce cos_slow)
    (ucFun2 cR cR cR cRplus_uc x0
      (cRopp
        (ucFun cR cR (unsafeCoerce compress)
          (ucFun cR cR
            (unsafeCoerce scale
              (qmult (plus q_plus (one q_1) (one q_1))
                (inject_Z
                  (qceiling
                    (qminus
                      (unsafeCoerce approximate q_as_MetricSpace
                        (cRmult x0
                          (ucFun cR cR
                            (unsafeCoerce cRinv_pos
                              (qposMake ((\x -> 2 Prelude.* x)
                                ((\x -> 2 Prelude.* x Prelude.+ 1) 1)) 1))
                            (ucFun cR cR
                              (unsafeCoerce scale
                                (plus q_plus (one q_1) (one q_1))) cRpi)))
                        (Qpos2QposInf
                        (qposMake 1 ((\x -> 2 Prelude.* x) 1))))
                      ((\x y -> (Data.Ratio.%) x y) ((\x -> x) 1)
                      ((\x -> 2 Prelude.* x) 1))))))) cRpi))))

cRpi_RealNumberPi_instance :: RealNumberPi St_car
cRpi_RealNumberPi_instance =
  cRpi

cR_Half_instance :: HalfNum St_car
cR_Half_instance =
  inject_Q_CR ((\x y -> (Data.Ratio.%) x y) ((\x -> x) 1)
    ((\x -> 2 Prelude.* x) 1))

q2Zapprox :: (Data.Ratio.Ratio Prelude.Integer) -> Prelude.Integer
q2Zapprox q =
  let {qf = qfloor q} in
  case decide
         (decision_instance_1 (qminus q (inject_Z qf))
           ((\x y -> (Data.Ratio.%) x y) ((\x -> x) 1) ((\x -> 2 Prelude.* x)
           1))) of {
   Prelude.True -> qf;
   Prelude.False -> (Prelude.+) qf ((\x -> x) 1)}

r2ZApprox :: St_car -> Qpos -> Prelude.Integer
r2ZApprox r eps0 =
  q2Zapprox (unsafeCoerce approximate q_as_MetricSpace r (Qpos2QposInf eps0))

type MinClass a = a -> a -> a

min0 :: (MinClass a1) -> a1 -> a1 -> a1
min0 minClass =
  minClass

type MaxClass a = a -> a -> a

max0 :: (MaxClass a1) -> a1 -> a1 -> a1
max0 maxClass =
  maxClass

type GSinClass b a = b -> a

type GCosClass b a = b -> a

type SinClass a = GSinClass a a

sin0 :: (SinClass a1) -> GSinClass a1 a1
sin0 sinClass =
  sinClass

type CosClass a = GCosClass a a

cos0 :: (CosClass a1) -> GCosClass a1 a1
cos0 cosClass =
  cosClass

type ApartT a apartT = apartT

type ReciprocalT a h0 = a -> (ApartT a h0) -> a

recipT :: (Zero a1) -> (ReciprocalT a1 a2) -> a1 -> (ApartT a1 a2) -> a1
recipT _ reciprocalT =
  reciprocalT

castPairLikeSame :: (a2 -> a2 -> a1) -> (a1 -> a2) -> (a1 -> a2) -> Cast 
                    a2 a1
castPairLikeSame mkpair _ _ p =
  mkpair p p

zeroPairLike :: (a2 -> a3 -> a1) -> (a1 -> a2) -> (a1 -> a3) -> (Zero 
                a2) -> (Zero a3) -> Zero a1
zeroPairLike mkpair _ _ h0 h1 =
  mkpair (zero h0) (zero h1)

plusPairLike :: (a2 -> a3 -> a1) -> (a1 -> a2) -> (a1 -> a3) -> (Plus 
                a2) -> (Plus a3) -> Plus a1
plusPairLike mkpair pfst psnd h0 h1 a b =
  mkpair (plus h0 (pfst a) (pfst b)) (plus h1 (psnd a) (psnd b))

multPairLike :: (a2 -> a3 -> a1) -> (a1 -> a2) -> (a1 -> a3) -> (Mult 
                a2) -> (Mult a3) -> Mult a1
multPairLike mkpair pfst psnd h0 h1 a b =
  mkpair (mult h0 (pfst a) (pfst b)) (mult h1 (psnd a) (psnd b))

unitVec :: (SinClass a1) -> (CosClass a1) -> a1 -> Cart2D a1
unitVec h h0 __U03b8_ =
  MkCart2D (cos0 h0 __U03b8_) (sin0 h __U03b8_)

data Rigid2DState a =
   Build_Rigid2DState (Cart2D a) a

pos2D :: (Rigid2DState a1) -> Cart2D a1
pos2D r =
  case r of {
   Build_Rigid2DState pos2D0 _ -> pos2D0}

__U03b8_2D :: (Rigid2DState a1) -> a1
__U03b8_2D r =
  case r of {
   Build_Rigid2DState _ __U03b8_2D0 -> __U03b8_2D0}

data Line2D a =
   Build_Line2D (Cart2D a) (Cart2D a)

lstart :: (Line2D a1) -> Cart2D a1
lstart l =
  case l of {
   Build_Line2D lstart0 _ -> lstart0}

lend :: (Line2D a1) -> Cart2D a1
lend l =
  case l of {
   Build_Line2D _ lend0 -> lend0}

llll1 :: Cast (Cart2D a1) (Line2D a1)
llll1 =
  castPairLikeSame (\x0 x1 -> Build_Line2D x0 x1) lstart lend

llll6 :: (Zero a1) -> Zero (Line2D a1)
llll6 azero =
  zeroPairLike (\x0 x1 -> Build_Line2D x0 x1) lstart lend
    (zero_instance_Cart2D azero) (zero_instance_Cart2D azero)

llll8 :: (Plus a1) -> Plus (Line2D a1)
llll8 aplus =
  plusPairLike (\x0 x1 -> Build_Line2D x0 x1) lstart lend
    (plus_instance_Cart2D aplus) (plus_instance_Cart2D aplus)

multLine :: (Mult a1) -> Mult (Line2D a1)
multLine amult =
  multPairLike (\x0 x1 -> Build_Line2D x0 x1) lstart lend
    (mutt_instance_Cart2D amult) (mutt_instance_Cart2D amult)

centredLineAtAngle :: (SinClass a1) -> (CosClass a1) -> (Plus a1) -> (Mult
                      a1) -> (Zero a1) -> (One a1) -> (Negate a1) -> a1 -> a1
                      -> (Cart2D a1) -> Line2D a1
centredLineAtAngle h h0 aplus amult _ _ anegate angle halfLength p =
  let {
   v = mult (mutt_instance_Cart2D amult) (cast castCRCart2DCR halfLength)
         (unitVec h h0 angle)}
  in
  Build_Line2D
  (plus (plus_instance_Cart2D aplus) p
    (negate (negate_instance_Cart2D anegate) v))
  (plus (plus_instance_Cart2D aplus) p v)

linesConsecutive :: (([]) (Cart2D a1)) -> ([]) (Line2D a1)
linesConsecutive pts =
  case pts of {
   ([]) -> ([]);
   (:) h1 tl0 ->
    case tl0 of {
     ([]) -> ([]);
     (:) h2 _ -> (:) (Build_Line2D h1 h2) (linesConsecutive tl0)}}

type BoundingRectangle a = Line2D a

minCart :: (MinClass a1) -> (Cart2D a1) -> (Cart2D a1) -> Cart2D a1
minCart h a b =
  MkCart2D (min0 h (x a) (x b)) (min0 h (y a) (y b))

maxCart :: (MaxClass a1) -> (Cart2D a1) -> (Cart2D a1) -> Cart2D a1
maxCart h a b =
  MkCart2D (max0 h (x a) (x b)) (max0 h (y a) (y b))

boundingUnion :: (MinClass a1) -> (MaxClass a1) -> (Line2D a1) -> (Line2D 
                 a1) -> Line2D a1
boundingUnion h h0 a b =
  Build_Line2D (minCart h (lstart a) (lstart b))
    (maxCart h0 (lend a) (lend b))

computeBoundingRect :: (MinClass a1) -> (MaxClass a1) -> (Zero a1) -> (([])
                       (Cart2D a1)) -> BoundingRectangle a1
computeBoundingRect h h0 h1 pts =
  case pts of {
   ([]) -> Build_Line2D (zero (zero_instance_Cart2D h1))
    (zero (zero_instance_Cart2D h1));
   (:) h2 tl0 ->
    case tl0 of {
     ([]) -> Build_Line2D h2 h2;
     (:) _ _ ->
      let {b = computeBoundingRect h h0 h1 tl0} in
      boundingUnion h h0 b (Build_Line2D h2 h2)}}

minClassZ :: MinClass Prelude.Integer
minClassZ =
  Prelude.min

maxClassZ :: MaxClass Prelude.Integer
maxClassZ =
  Prelude.max

data CarDimensions a =
   Build_CarDimensions a a a

lengthFront :: (CarDimensions a1) -> a1
lengthFront c =
  case c of {
   Build_CarDimensions lengthFront0 _ _ -> lengthFront0}

lengthBack :: (CarDimensions a1) -> a1
lengthBack c =
  case c of {
   Build_CarDimensions _ lengthBack0 _ -> lengthBack0}

width :: (CarDimensions a1) -> a1
width c =
  case c of {
   Build_CarDimensions _ _ width0 -> width0}

totalLength :: (Plus a1) -> (CarDimensions a1) -> a1
totalLength h cd =
  plus h (lengthFront cd) (lengthBack cd)

frontUnitVec :: (SinClass a1) -> (CosClass a1) -> (Rigid2DState a1) -> Cart2D
                a1
frontUnitVec h h0 cs =
  unitVec h h0 (__U03b8_2D cs)

rightSideUnitVec :: (SinClass a1) -> (CosClass a1) -> (Plus a1) -> (Mult 
                    a1) -> (Negate a1) -> (RealNumberPi a1) -> (HalfNum 
                    a1) -> (Rigid2DState a1) -> Cart2D a1
rightSideUnitVec h h0 aplus amult anegate h2 h3 cs =
  unitVec h h0
    (plus aplus (__U03b8_2D cs)
      (negate anegate (mult amult (half_num h3) (__U03c0_ h2))))

frontRight :: (SinClass a1) -> (CosClass a1) -> (Plus a1) -> (Mult a1) ->
              (Negate a1) -> (RealNumberPi a1) -> (HalfNum a1) ->
              (CarDimensions a1) -> (Rigid2DState a1) -> Cart2D a1
frontRight h h0 aplus amult anegate h2 h3 cd cs =
  plus (plus_instance_Cart2D aplus) (pos2D cs)
    (plus (plus_instance_Cart2D aplus)
      (mult (mutt_instance_Cart2D amult) (frontUnitVec h h0 cs)
        (cast castCRCart2DCR (lengthFront cd)))
      (mult (mutt_instance_Cart2D amult)
        (rightSideUnitVec h h0 aplus amult anegate h2 h3 cs)
        (cast castCRCart2DCR (width cd))))

frontLeft :: (SinClass a1) -> (CosClass a1) -> (Plus a1) -> (Mult a1) ->
             (Negate a1) -> (RealNumberPi a1) -> (HalfNum a1) ->
             (CarDimensions a1) -> (Rigid2DState a1) -> Cart2D a1
frontLeft h h0 aplus amult anegate h2 h3 cd cs =
  plus (plus_instance_Cart2D aplus) (pos2D cs)
    (plus (plus_instance_Cart2D aplus)
      (mult (mutt_instance_Cart2D amult) (frontUnitVec h h0 cs)
        (cast castCRCart2DCR (lengthFront cd)))
      (negate (negate_instance_Cart2D anegate)
        (mult (mutt_instance_Cart2D amult)
          (rightSideUnitVec h h0 aplus amult anegate h2 h3 cs)
          (cast castCRCart2DCR (width cd)))))

backLeft :: (SinClass a1) -> (CosClass a1) -> (Plus a1) -> (Mult a1) ->
            (Negate a1) -> (RealNumberPi a1) -> (HalfNum a1) ->
            (CarDimensions a1) -> (Rigid2DState a1) -> Cart2D a1
backLeft h h0 aplus amult anegate h2 h3 cd cs =
  plus (plus_instance_Cart2D aplus) (pos2D cs)
    (plus (plus_instance_Cart2D aplus)
      (mult (mutt_instance_Cart2D amult)
        (negate (negate_instance_Cart2D anegate) (frontUnitVec h h0 cs))
        (cast castCRCart2DCR (lengthBack cd)))
      (negate (negate_instance_Cart2D anegate)
        (mult (mutt_instance_Cart2D amult)
          (rightSideUnitVec h h0 aplus amult anegate h2 h3 cs)
          (cast castCRCart2DCR (width cd)))))

backRight :: (SinClass a1) -> (CosClass a1) -> (Plus a1) -> (Mult a1) ->
             (Negate a1) -> (RealNumberPi a1) -> (HalfNum a1) ->
             (CarDimensions a1) -> (Rigid2DState a1) -> Cart2D a1
backRight h h0 aplus amult anegate h2 h3 cd cs =
  plus (plus_instance_Cart2D aplus) (pos2D cs)
    (plus (plus_instance_Cart2D aplus)
      (mult (mutt_instance_Cart2D amult)
        (negate (negate_instance_Cart2D anegate) (frontUnitVec h h0 cs))
        (cast castCRCart2DCR (lengthBack cd)))
      (mult (mutt_instance_Cart2D amult)
        (rightSideUnitVec h h0 aplus amult anegate h2 h3 cs)
        (cast castCRCart2DCR (width cd))))

carOutline :: (SinClass a1) -> (CosClass a1) -> (Plus a1) -> (Mult a1) ->
              (Negate a1) -> (RealNumberPi a1) -> (HalfNum a1) ->
              (CarDimensions a1) -> (Rigid2DState a1) -> ([]) (Line2D a1)
carOutline h h0 aplus amult anegate h2 h3 cd cs =
  (:) (Build_Line2D (frontRight h h0 aplus amult anegate h2 h3 cd cs)
    (backRight h h0 aplus amult anegate h2 h3 cd cs))
    (linesConsecutive ((:) (frontRight h h0 aplus amult anegate h2 h3 cd cs)
      ((:) (frontLeft h h0 aplus amult anegate h2 h3 cd cs) ((:)
      (backLeft h h0 aplus amult anegate h2 h3 cd cs) ((:)
      (backRight h h0 aplus amult anegate h2 h3 cd cs) ([]))))))

castCarDim :: (Cast a1 a2) -> Cast (CarDimensions a1) (CarDimensions a2)
castCarDim h a =
  Build_CarDimensions (cast h (lengthFront a)) (cast h (lengthBack a))
    (cast h (width a))

data AtomicMove r =
   MkAtomicMove r r

am_distance :: (AtomicMove a1) -> a1
am_distance a =
  case a of {
   MkAtomicMove am_distance0 _ -> am_distance0}

am_tc :: (AtomicMove a1) -> a1
am_tc a =
  case a of {
   MkAtomicMove _ am_tc0 -> am_tc0}

type AtomicMoveSign r h0 = Prelude.Either () (ApartT r h0)

type DAtomicMove r h0 = SigT (AtomicMove r) (AtomicMoveSign r h0)

stateAfterAtomicMove :: (Plus a1) -> (Mult a1) -> (Zero a1) -> (One a1) ->
                        (Negate a1) -> (Zero a1) -> (ReciprocalT a1 a3) ->
                        (SinClass a1) -> (CosClass a1) -> (Rigid2DState 
                        a1) -> (DAtomicMove a1 a3) -> Rigid2DState a1
stateAfterAtomicMove aplus amult _ _ anegate h1 h3 h4 h5 cs dm =
  let {tc = am_tc (projT1 dm)} in
  let {dist = am_distance (projT1 dm)} in
  let {__U03b8_Init = __U03b8_2D cs} in
  let {__U03b8_f = plus aplus __U03b8_Init (mult amult tc dist)} in
  let {posInit = pos2D cs} in
  let {
   posDelta = case projT2 dm of {
               Prelude.Left _ ->
                mult (mutt_instance_Cart2D amult) (cast castCRCart2DCR dist)
                  (unitVec h4 h5 __U03b8_Init);
               Prelude.Right p -> MkCart2D
                (mult amult
                  (plus aplus (sin0 h4 __U03b8_f)
                    (negate anegate (sin0 h4 __U03b8_Init)))
                  (recipT h1 h3 tc p))
                (mult amult
                  (plus aplus (cos0 h5 __U03b8_Init)
                    (negate anegate (cos0 h5 __U03b8_f)))
                  (recipT h1 h3 tc p))}}
  in
  Build_Rigid2DState (plus (plus_instance_Cart2D aplus) posInit posDelta)
  __U03b8_f

zero0 :: Prelude.Char
zero0 =
  '\000'

one0 :: Prelude.Char
one0 =
  '\001'

shift :: Prelude.Bool -> Prelude.Char -> Prelude.Char
shift c a =
  (\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0)
              (Data.Bits.testBit (Data.Char.ord a) 1)
              (Data.Bits.testBit (Data.Char.ord a) 2)
              (Data.Bits.testBit (Data.Char.ord a) 3)
              (Data.Bits.testBit (Data.Char.ord a) 4)
              (Data.Bits.testBit (Data.Char.ord a) 5)
              (Data.Bits.testBit (Data.Char.ord a) 6)
              (Data.Bits.testBit (Data.Char.ord a) 7))
    (\a1 a2 a3 a4 a5 a6 a7 _ ->
    (\b0 b1 b2 b3 b4 b5 b6 b7 -> Data.Char.chr (
      (if b0 then Data.Bits.shiftL 1 0 else 0) Prelude.+
      (if b1 then Data.Bits.shiftL 1 1 else 0) Prelude.+
      (if b2 then Data.Bits.shiftL 1 2 else 0) Prelude.+
      (if b3 then Data.Bits.shiftL 1 3 else 0) Prelude.+
      (if b4 then Data.Bits.shiftL 1 4 else 0) Prelude.+
      (if b5 then Data.Bits.shiftL 1 5 else 0) Prelude.+
      (if b6 then Data.Bits.shiftL 1 6 else 0) Prelude.+
      (if b7 then Data.Bits.shiftL 1 7 else 0)))
    c a1 a2 a3 a4 a5 a6
    a7)
    a

ascii_of_pos :: Prelude.Integer -> Prelude.Char
ascii_of_pos =
  let {
   loop n p =
     (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
       (\_ ->
       zero0)
       (\n' ->
       (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
         (\p' ->
         shift Prelude.True (loop n' p'))
         (\p' ->
         shift Prelude.False (loop n' p'))
         (\_ ->
         one0)
         p)
       n}
  in loop (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
       (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))

ascii_of_N :: N -> Prelude.Char
ascii_of_N n =
  case n of {
   N0 -> zero0;
   Npos p -> ascii_of_pos p}

ascii_of_nat :: Prelude.Integer -> Prelude.Char
ascii_of_nat a =
  ascii_of_N (of_nat a)

append :: Prelude.String -> Prelude.String -> Prelude.String
append s1 s2 =
  case s1 of {
   ([]) -> s2;
   (:) c s1' -> (:) c (append s1' s2)}

posCompareContAbstract43820948120402312 :: Prelude.Ordering ->
                                           Prelude.Integer -> Prelude.Integer
                                           -> Prelude.Ordering
posCompareContAbstract43820948120402312 c x0 y0 =
  switch_Eq c ((Prelude.compare) x0 y0)

sinClassCR :: SinClass St_car
sinClassCR =
  sin

cosClassCR :: CosClass St_car
cosClassCR =
  cos

type ApartTCR = CRapartT

recipTCR :: ReciprocalT St_car ApartTCR
recipTCR =
  cRinvT

data CarGeometry a =
   Build_CarGeometry (CarDimensions a) a

carDim :: (CarGeometry a1) -> CarDimensions a1
carDim c =
  case c of {
   Build_CarGeometry carDim0 _ -> carDim0}

minTR :: (CarGeometry a1) -> a1
minTR c =
  case c of {
   Build_CarGeometry _ minTR0 -> minTR0}

mazda3Sedan2014sGT_Dim :: CarDimensions Prelude.Integer
mazda3Sedan2014sGT_Dim =
  Build_CarDimensions ((\x -> x) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
    ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))))) ((\x -> x)
    ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x) 1)))))) ((\x -> x)
    ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x) 1))))))

mazda3Sedan2014sGT :: CarGeometry Prelude.Integer
mazda3Sedan2014sGT =
  Build_CarGeometry mazda3Sedan2014sGT_Dim ((\x -> x) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
    ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
    ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))))))))

data CarState a =
   Build_carState (Rigid2DState a) a

csrigid2D :: (CarState a1) -> Rigid2DState a1
csrigid2D c =
  case c of {
   Build_carState csrigid2D0 _ -> csrigid2D0}

cs_tc :: (CarState a1) -> a1
cs_tc c =
  case c of {
   Build_carState _ cs_tc0 -> cs_tc0}

sFmapCart2D :: (a1 -> a2) -> (Cart2D a1) -> Cart2D a2
sFmapCart2D f c =
  MkCart2D (f (x c)) (f (y c))

carStateAfterAtomicMove :: (CarState St_car) -> (DAtomicMove St_car ApartTCR)
                           -> CarState St_car
carStateAfterAtomicMove cs dm =
  Build_carState
    (stateAfterAtomicMove cRplus cRmult cR0 cR1 cRopp cR0 recipTCR sinClassCR
      cosClassCR (csrigid2D cs) dm) (am_tc (projT1 dm))

castZCR :: Cast Prelude.Integer St_car
castZCR x0 =
  inject_Q_CR (inject_Z x0)

finerRes :: Prelude.Integer
finerRes =
  (\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))

roundPointRZ :: Qpos -> (Cart2D St_car) -> Cart2D Prelude.Integer
roundPointRZ eps0 p =
  MkCart2D (r2ZApprox (mult cRmult (cast castZCR finerRes) (x p)) eps0)
    (r2ZApprox (mult cRmult (cast castZCR finerRes) (y p)) eps0)

roundLineRZ :: Qpos -> (Line2D St_car) -> Line2D Prelude.Integer
roundLineRZ eps0 p =
  Build_Line2D (roundPointRZ eps0 (lstart p)) (roundPointRZ eps0 (lend p))

ztoString :: Prelude.Integer -> Prelude.String
ztoString x =
        let (q,r) = Prelude.quotRem x 100 in
        let rs = (Prelude.show (Prelude.abs r)) in
        let rss = (if ((Prelude.<) (Prelude.abs r) 10) then Prelude.concat ["0",rs] else rs) in
        let out = Prelude.concat [(Prelude.show q), ".",rss] in
        (if ((Prelude.&&) ((Prelude.==) q 0) ((Prelude.<) r 0)) then Prelude.concat ["-", out] else out)

sconcat :: (([]) Prelude.String) -> Prelude.String
sconcat l =
  fold_left append l ([])

newLineChar :: Prelude.Char
newLineChar =
  ascii_of_nat (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ 0))))))))))

newLineString :: Prelude.String
newLineString =
  (:) newLineChar ([])

tikZPoint :: (Cart2D Prelude.Integer) -> Prelude.String
tikZPoint p =
  append ((:) '(' ([]))
    (append (ztoString (x p))
      (append ((:) ',' ([])) (append (ztoString (y p)) ((:) ')' ([])))))

tikZLine :: (Line2D Prelude.Integer) -> Prelude.String
tikZLine l =
  append ((:) '\\' ((:) 'd' ((:) 'r' ((:) 'a' ((:) 'w' ([]))))))
    (append (tikZPoint (lstart l))
      (append ((:) '-' ((:) '-' ([])))
        (append (tikZPoint (lend l)) (append ((:) ';' ([])) newLineString))))

tikZLineStyled :: Prelude.String -> (Line2D Prelude.Integer) ->
                  Prelude.String
tikZLineStyled s l =
  sconcat ((:) ((:) '\\' ((:) 'd' ((:) 'r' ((:) 'a' ((:) 'w' ((:) '['
    ([]))))))) ((:) s ((:) ((:) ']' ([])) ((:) (tikZPoint (lstart l)) ((:)
    ((:) '-' ((:) '-' ([]))) ((:) (tikZPoint (lend l)) ((:) ((:) ';' ([]))
    ((:) newLineString ([])))))))))

tikZFilledRect :: Prelude.String -> (Line2D Prelude.Integer) ->
                  Prelude.String
tikZFilledRect color l =
  append ((:) '\\' ((:) 'd' ((:) 'r' ((:) 'a' ((:) 'w' ((:) '[' ((:) 'f' ((:)
    'i' ((:) 'l' ((:) 'l' ((:) '=' ([]))))))))))))
    (append color
      (append ((:) ',' ([]))
        (append color
          (append ((:) ',' ((:) ' ' ((:) 'f' ((:) 'i' ((:) 'l' ((:) 'l' ((:)
            ' ' ((:) 'o' ((:) 'p' ((:) 'a' ((:) 'c' ((:) 'i' ((:) 't' ((:)
            'y' ((:) '=' ((:) '0' ((:) '.' ((:) '3' ((:) ']'
            ([]))))))))))))))))))))
            (append (tikZPoint (lstart l))
              (append ((:) ' ' ((:) 'r' ((:) 'e' ((:) 'c' ((:) 't' ((:) 'a'
                ((:) 'n' ((:) 'g' ((:) 'l' ((:) 'e' ((:) ' ' ([]))))))))))))
                (append (tikZPoint (lend l))
                  (append ((:) ';' ([])) newLineString))))))))

tikZColoredLine :: Prelude.String -> (Line2D Prelude.Integer) ->
                   Prelude.String
tikZColoredLine color l =
  append ((:) '\\' ((:) 'd' ((:) 'r' ((:) 'a' ((:) 'w' ((:) '[' ([])))))))
    (append color
      (append ((:) ']' ([]))
        (append (tikZPoint (lstart l))
          (append ((:) '-' ((:) '-' ([])))
            (append (tikZPoint (lend l))
              (append ((:) ';' ([])) newLineString))))))

tikZLines :: (([]) (Line2D Prelude.Integer)) -> Prelude.String
tikZLines l =
  sconcat (map tikZLine l)

computeBoundingRectLines :: (MinClass a1) -> (MaxClass a1) -> (Zero a1) ->
                            (([]) (Line2D a1)) -> BoundingRectangle a1
computeBoundingRectLines h h0 h1 ll =
  computeBoundingRect h h0 h1 (app (map lstart ll) (map lend ll))

tikZBoundingClip :: (BoundingRectangle Prelude.Integer) -> Prelude.String
tikZBoundingClip l =
  append ((:) '\\' ((:) 'c' ((:) 'l' ((:) 'i' ((:) 'p' ([]))))))
    (append (tikZPoint (lstart l))
      (append ((:) ' ' ((:) 'r' ((:) 'e' ((:) 'c' ((:) 't' ((:) 'a' ((:) 'n'
        ((:) 'g' ((:) 'l' ((:) 'e' ((:) ' ' ([]))))))))))))
        (append (tikZPoint (lend l)) (append ((:) ';' ([])) newLineString))))

castQCartCR :: Cast (Data.Ratio.Ratio Prelude.Integer) (Cart2D St_car)
castQCartCR x0 =
  sameXY (inject_Q_CR x0)

leftWheelCenter :: (CarDimensions St_car) -> (Rigid2DState St_car) -> Cart2D
                   St_car
leftWheelCenter cd cs =
  plus (plus_instance_Cart2D cRplus) (pos2D cs)
    (mult (mutt_instance_Cart2D cRmult)
      (cast castQCartCR ((\x y -> (Data.Ratio.%) x y) ((\x -> x)
        ((\x -> 2 Prelude.* x Prelude.+ 1) 1)) ((\x -> 2 Prelude.* x)
        ((\x -> 2 Prelude.* x) 1))))
      (plus (plus_instance_Cart2D cRplus)
        (mult (mutt_instance_Cart2D cRmult)
          (frontUnitVec sinClassCR cosClassCR cs)
          (cast castCRCart2DCR (lengthFront cd)))
        (mult (mutt_instance_Cart2D cRmult)
          (rightSideUnitVec sinClassCR cosClassCR cRplus cRmult cRopp
            cRpi_RealNumberPi_instance cR_Half_instance cs)
          (cast castCRCart2DCR (width cd)))))

rightWheelCenter :: (CarDimensions St_car) -> (Rigid2DState St_car) -> Cart2D
                    St_car
rightWheelCenter cd cs =
  plus (plus_instance_Cart2D cRplus) (pos2D cs)
    (mult (mutt_instance_Cart2D cRmult)
      (cast castQCartCR ((\x y -> (Data.Ratio.%) x y) ((\x -> x)
        ((\x -> 2 Prelude.* x Prelude.+ 1) 1)) ((\x -> 2 Prelude.* x)
        ((\x -> 2 Prelude.* x) 1))))
      (plus (plus_instance_Cart2D cRplus)
        (mult (mutt_instance_Cart2D cRmult)
          (frontUnitVec sinClassCR cosClassCR cs)
          (cast castCRCart2DCR (lengthFront cd)))
        (negate (negate_instance_Cart2D cRopp)
          (mult (mutt_instance_Cart2D cRmult)
            (rightSideUnitVec sinClassCR cosClassCR cRplus cRmult cRopp
              cRpi_RealNumberPi_instance cR_Half_instance cs)
            (cast castCRCart2DCR (width cd))))))

carWheels :: (CarDimensions St_car) -> (Rigid2DState St_car) -> St_car ->
             ([]) (Line2D St_car)
carWheels cd cs __U03b1_ =
  map
    (centredLineAtAngle sinClassCR cosClassCR cRplus cRmult cR0 cR1 cRopp
      __U03b1_
      (mult cRmult (lengthFront cd)
        (cast inject_Q_CR ((\x y -> (Data.Ratio.%) x y) ((\x -> x) 1)
          ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
          ((\x -> 2 Prelude.* x) 1))))))) ((:) (leftWheelCenter cd cs) ((:)
    (rightWheelCenter cd cs) ([])))

drawCarZAux :: Qpos -> (CarDimensions St_car) -> (Rigid2DState St_car) ->
               St_car -> ([]) (Line2D Prelude.Integer)
drawCarZAux eps0 cd cs __U03b1_ =
  map (roundLineRZ eps0)
    (app
      (carOutline sinClassCR cosClassCR cRplus cRmult cRopp
        cRpi_RealNumberPi_instance cR_Half_instance cd cs)
      (carWheels cd cs __U03b1_))

angleLineLength :: (CarDimensions St_car) -> St_car
angleLineLength cd =
  mult cRmult
    (cast inject_Q_CR ((\x y -> (Data.Ratio.%) x y) ((\x -> x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))) (totalLength cRplus cd)

angleLineXLength :: (CarDimensions St_car) -> St_car
angleLineXLength cd =
  angleLineLength cd

type Pair t = (,) t t

angleLines :: (CarDimensions St_car) -> (Rigid2DState St_car) -> Pair
              (Line2D St_car)
angleLines cd cs =
  let {
   ls = plus (plus_instance_Cart2D cRplus) (pos2D cs)
          (negate (negate_instance_Cart2D cRopp)
            (mult (mutt_instance_Cart2D cRmult)
              (cast castCRCart2DCR (lengthBack cd))
              (frontUnitVec sinClassCR cosClassCR cs)))}
  in
  (,) (Build_Line2D ls
  (plus (plus_instance_Cart2D cRplus) ls
    (mult (mutt_instance_Cart2D cRmult)
      (cast castCRCart2DCR (angleLineLength cd))
      (frontUnitVec sinClassCR cosClassCR cs)))) (Build_Line2D ls
  (plus (plus_instance_Cart2D cRplus) ls (MkCart2D (angleLineXLength cd)
    (zero cR0))))

textPos :: (CarDimensions St_car) -> (Rigid2DState St_car) -> Cart2D St_car
textPos cd cs =
  plus (plus_instance_Cart2D cRplus) (pos2D cs)
    (mult (mutt_instance_Cart2D cRmult)
      (cast castCRCart2DCR (totalLength cRplus cd))
      (unitVec sinClassCR cosClassCR
        (mult cRmult (half_num cR_Half_instance) (__U03b8_2D cs))))

angleLabel :: Qpos -> (CarDimensions St_car) -> (Rigid2DState St_car) ->
              Prelude.String -> Prelude.String
angleLabel eps0 cd cs label =
  sconcat ((:) ((:) '\\' ((:) 'n' ((:) 'o' ((:) 'd' ((:) 'e' ((:) '[' ((:)
    'r' ((:) 'i' ((:) 'g' ((:) 'h' ((:) 't' ((:) ']' ((:) ' ' ((:) 'a' ((:)
    't' ((:) ' ' ([]))))))))))))))))) ((:)
    (tikZPoint (roundPointRZ eps0 (textPos cd cs))) ((:) ((:) '{' ([])) ((:)
    label ((:) ((:) '}' ((:) ';' ([]))) ([]))))))

illustrateAngle :: Qpos -> (CarDimensions St_car) -> (Rigid2DState St_car) ->
                   Prelude.String -> Prelude.String
illustrateAngle eps0 cd cs alabel =
  sconcat ((:)
    (tikZLineStyled ((:) 'd' ((:) 'a' ((:) 's' ((:) 'h' ((:) 'e' ((:) 'd'
      ([]))))))) (roundLineRZ eps0 (fst (angleLines cd cs)))) ((:)
    (tikZLineStyled ((:) 'd' ((:) 'o' ((:) 't' ((:) 't' ((:) 'e' ((:) 'd'
      ([]))))))) (roundLineRZ eps0 (snd (angleLines cd cs)))) ((:)
    (angleLabel eps0 cd cs alabel) ([]))))

comparisonAsZ :: Prelude.Ordering -> Prelude.Integer
comparisonAsZ c =
  case c of {
   Prelude.EQ -> 0;
   Prelude.LT -> Prelude.negate 1;
   Prelude.GT -> (\x -> x) 1}

data CarStateRenderingInfo =
   Build_CarStateRenderingInfo Prelude.String Prelude.Bool Prelude.String 
 Prelude.Bool Prelude.Bool

frameLabel :: CarStateRenderingInfo -> Prelude.String
frameLabel c =
  case c of {
   Build_CarStateRenderingInfo frameLabel0 _ _ _ _ -> frameLabel0}

drawAngle :: CarStateRenderingInfo -> Prelude.Bool
drawAngle c =
  case c of {
   Build_CarStateRenderingInfo _ drawAngle0 _ _ _ -> drawAngle0}

angleString :: CarStateRenderingInfo -> Prelude.String
angleString c =
  case c of {
   Build_CarStateRenderingInfo _ _ angleString0 _ _ -> angleString0}

pauseBefore :: CarStateRenderingInfo -> Prelude.Bool
pauseBefore c =
  case c of {
   Build_CarStateRenderingInfo _ _ _ pauseBefore0 _ -> pauseBefore0}

mkRenderingInfo :: (Pair Prelude.String) -> CarStateRenderingInfo
mkRenderingInfo name =
  Build_CarStateRenderingInfo (fst name) Prelude.False (snd name)
    Prelude.False Prelude.False

mkTransitionRenderingInfo :: (Pair Prelude.String) -> CarStateRenderingInfo
mkTransitionRenderingInfo name =
  Build_CarStateRenderingInfo (fst name) Prelude.False (snd name) Prelude.True
    Prelude.False

wheelAngle :: (CarState St_car) -> St_car
wheelAngle cs =
  plus cRplus (__U03b8_2D (csrigid2D cs))
    (mult cRmult
      (mult cRmult
        (cast castZCR
          (comparisonAsZ
            (cR_epsilon_sign_dec
              (qposMake 1 ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
                ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
                ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
                ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
                ((\x -> 2 Prelude.* x Prelude.+ 1)
                ((\x -> 2 Prelude.* x Prelude.+ 1)
                ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
                ((\x -> 2 Prelude.* x) 1)))))))))))))) (cs_tc cs))))
        (cast inject_Q_CR ((\x y -> (Data.Ratio.%) x y) ((\x -> x) 1)
          ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))))
      (__U03c0_ cRpi_RealNumberPi_instance))

drawCarZ :: Qpos -> (CarDimensions St_car) -> (CarState St_car) -> ([])
            (Line2D Prelude.Integer)
drawCarZ eps0 cd cs =
  drawCarZAux eps0 cd (csrigid2D cs) (wheelAngle cs)

eps :: Qpos
eps =
  qposMake 1 ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))

myCarDimZ :: (CarGeometry Prelude.Integer) -> CarDimensions Prelude.Integer
myCarDimZ carGeo =
  carDim carGeo

myCarDim :: (CarGeometry Prelude.Integer) -> CarDimensions St_car
myCarDim carGeo =
  cast (castCarDim castZCR) (myCarDimZ carGeo)

initSt :: CarState St_car
initSt =
  Build_carState (Build_Rigid2DState (zero (zero_instance_Cart2D cR0))
    (zero cR0)) (zero cR0)

type NamedCarState = (,) CarStateRenderingInfo (CarState St_car)

drawCarFrameZ :: (CarGeometry Prelude.Integer) -> NamedCarState -> (,)
                 ((,) Prelude.String Prelude.String)
                 (([]) (Line2D Prelude.Integer))
drawCarFrameZ carGeo ns =
  let {
   newF = case pauseBefore (fst ns) of {
           Prelude.True -> (:) '\\' ((:) 'n' ((:) 'e' ((:) 'w' ((:) 'f' ((:)
            'r' ((:) 'a' ((:) 'm' ((:) 'e' ((:) '*' ([]))))))))));
           Prelude.False -> (:) '\\' ((:) 'n' ((:) 'e' ((:) 'w' ((:) 'f' ((:)
            'r' ((:) 'a' ((:) 'm' ((:) 'e' ([])))))))))}}
  in
  let {
   angle = illustrateAngle eps (myCarDim carGeo) (csrigid2D (snd ns))
             (angleString (fst ns))}
  in
  let {
   angle0 = case drawAngle (fst ns) of {
             Prelude.True -> angle;
             Prelude.False -> ([])}}
  in
  (,) ((,) (frameLabel (fst ns))
  (sconcat ((:) angle0 ((:) newF ((:) newLineString ([]))))))
  (drawCarZ eps (myCarDim carGeo) (snd ns))

carStatesFrames :: (CarGeometry Prelude.Integer) -> (([]) NamedCarState) ->
                   ([])
                   ((,) ((,) Prelude.String Prelude.String)
                   (([]) (Line2D Prelude.Integer)))
carStatesFrames carGeo l =
  map (drawCarFrameZ carGeo) l

getAtomicMove :: (DAtomicMove St_car ApartTCR) -> AtomicMove St_car
getAtomicMove d =
  projT1 d

type NameDAtomicMove =
  (,) (Pair Prelude.String) (DAtomicMove St_car ApartTCR)

scaleAtomicMove :: (AtomicMove St_car) -> St_car -> AtomicMove St_car
scaleAtomicMove m s =
  MkAtomicMove (mult cRmult s (am_distance m)) (am_tc m)

dscaleAtomicMove :: (DAtomicMove St_car ApartTCR) ->
                    (Data.Ratio.Ratio Prelude.Integer) -> DAtomicMove 
                    St_car ApartTCR
dscaleAtomicMove m s =
  ExistT (scaleAtomicMove (getAtomicMove m) (inject_Q_CR s)) (projT2 m)

finerAtomicMoves :: Prelude.Integer -> (DAtomicMove St_car ApartTCR) -> ([])
                    (DAtomicMove St_car ApartTCR)
finerAtomicMoves d m =
  map (dscaleAtomicMove m) (equiMidPoints d)

finerStates :: Prelude.Integer -> NameDAtomicMove -> (CarState St_car) -> (,)
               NamedCarState (([]) NamedCarState)
finerStates d dm init =
  case dm of {
   (,) name dm0 -> (,) ((,) (mkTransitionRenderingInfo name)
    (carStateAfterAtomicMove init dm0))
    (map (\m -> (,) (mkRenderingInfo name) (carStateAfterAtomicMove init m))
      (finerAtomicMoves d dm0))}

finerMovesStates :: Prelude.Integer -> (([]) NameDAtomicMove) ->
                    NamedCarState -> ([]) NamedCarState
finerMovesStates d l init =
  case l of {
   ([]) -> (:) init ([]);
   (:) hm t ->
    case finerStates d hm (snd init) of {
     (,) midState interS ->
      app ((:) init ([])) (app interS (finerMovesStates d t midState))}}

textHt :: Prelude.Integer
textHt =
  (Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
    ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))) finerRes

type Rect2D a = Line2D a

sideCars :: (CarGeometry Prelude.Integer) -> (BoundingRectangle
            Prelude.Integer) -> (BoundingRectangle Prelude.Integer) -> (,)
            (BoundingRectangle Prelude.Integer)
            (([]) (Rect2D Prelude.Integer))
sideCars carGeo global init =
  let {
   cardim = mult (mutt_instance_Cart2D z_mult) (sameXY finerRes) (MkCart2D
              (lengthFront (myCarDimZ carGeo))
              (mult z_mult (plus z_plus (one z_1) (one z_1))
                (width (myCarDimZ carGeo))))}
  in
  let {ymax = y (lend init)} in
  let {lcarMaxXY = MkCart2D (x (lstart global)) ymax} in
  let {
   rcarMinXY = MkCart2D (x (lend global))
    (plus z_plus ymax (negate z_negate (y cardim)))}
  in
  (,)
  (boundingUnion minClassZ maxClassZ global (Build_Line2D
    (plus (plus_instance_Cart2D z_plus) lcarMaxXY
      (negate (negate_instance_Cart2D z_negate) cardim))
    (plus (plus_instance_Cart2D z_plus) rcarMinXY cardim))) ((:)
  (Build_Line2D
  (plus (plus_instance_Cart2D z_plus) lcarMaxXY
    (negate (negate_instance_Cart2D z_negate) cardim)) lcarMaxXY) ((:)
  (Build_Line2D rcarMinXY
  (plus (plus_instance_Cart2D z_plus) rcarMinXY cardim)) ([])))

extendRectForText :: (BoundingRectangle Prelude.Integer) -> BoundingRectangle
                     Prelude.Integer
extendRectForText b =
  Build_Line2D
    (plus (plus_instance_Cart2D z_plus) (lstart b)
      (negate (negate_instance_Cart2D z_negate) (MkCart2D (zero z_0) textHt)))
    (plus (plus_instance_Cart2D z_plus) (lend b) (MkCart2D (zero z_0)
      textHt))

drawEnv :: (CarGeometry Prelude.Integer) -> (BoundingRectangle
           Prelude.Integer) -> (BoundingRectangle Prelude.Integer) -> (,)
           Prelude.String (Cart2D Prelude.Integer)
drawEnv carGeo global init =
  case sideCars carGeo global init of {
   (,) bc sc ->
    let {textPos0 = lstart bc} in
    let {bf = extendRectForText bc} in
    let {bottomLineStart = MkCart2D (x (lstart bc)) (y (lstart bc))} in
    let {bottomLineEnd = MkCart2D (x (lend bc)) (y (lstart bc))} in
    let {bottomLineZ = Build_Line2D bottomLineStart bottomLineEnd} in
    let {clip = tikZBoundingClip bf} in
    let {
     sideCars0 = map (tikZFilledRect ((:) 'r' ((:) 'e' ((:) 'd' ([]))))) sc}
    in
    let {
     bottomLine = tikZColoredLine ((:) 'r' ((:) 'e' ((:) 'd' ([]))))
                    bottomLineZ}
    in
    (,) (sconcat (app sideCars0 ((:) clip ((:) bottomLine ([]))))) textPos0}

frameWithLines :: Prelude.String -> (([]) (Line2D Prelude.Integer)) ->
                  Prelude.String
frameWithLines suffix lines =
  sconcat ((:) newLineString ((:) (tikZLines lines) ((:) newLineString ((:)
    suffix ((:) newLineString ([]))))))

fold_left_inter :: (a1 -> a2 -> a1) -> (([]) a2) -> a1 -> ([]) a1
fold_left_inter f l a0 =
  case l of {
   ([]) -> (:) a0 ([]);
   (:) b t -> (:) (f a0 b) (fold_left_inter f t (f a0 b))}

mkDAtomicMoveQ :: (AtomicMove (Data.Ratio.Ratio Prelude.Integer)) ->
                  DAtomicMove St_car ApartTCR
mkDAtomicMoveQ qa =
  case qa of {
   MkAtomicMove am_distance0 am_tc0 -> ExistT (MkAtomicMove
    (cast inject_Q_CR am_distance0) (cast inject_Q_CR am_tc0))
    (let {qd = qeq_bool am_tc0 ((\x y -> (Data.Ratio.%) x y) 0 1)} in
     case qd of {
      Prelude.True -> Prelude.Left __;
      Prelude.False -> Prelude.Right
       (qap_CRap am_tc0 ((\x y -> (Data.Ratio.%) x y) 0 1))})}

mkRelativeMove :: (CarGeometry Prelude.Integer) -> ((,)
                  (Data.Ratio.Ratio Prelude.Integer)
                  (Data.Ratio.Ratio Prelude.Integer)) -> DAtomicMove 
                  St_car ApartTCR
mkRelativeMove carGeo rel =
  case rel of {
   (,) turnCurv distance ->
    mkDAtomicMoveQ (MkAtomicMove
      (qmult distance (inject_Z (width (myCarDimZ carGeo))))
      (qdiv turnCurv (inject_Z (minTR carGeo))))}

mkNamedRelativeMove :: (CarGeometry Prelude.Integer) -> ((,)
                       (Data.Ratio.Ratio Prelude.Integer)
                       (Data.Ratio.Ratio Prelude.Integer)) -> NameDAtomicMove
mkNamedRelativeMove carGeo rel =
  (,) ((,) ([]) ([])) (mkRelativeMove carGeo rel)

relGlobalBound :: (CarGeometry Prelude.Integer) -> (BoundingRectangle
                  Prelude.Integer) -> (BoundingRectangle
                  (Data.Ratio.Ratio Prelude.Integer)) -> BoundingRectangle
                  Prelude.Integer
relGlobalBound carGeo initb extra0 =
  let {
   extra1 = mult (multLine q_mult)
              (cast llll1 (cast castCRCart2DCR (cast inject_Z_Q finerRes)))
              extra0}
  in
  let {
   rightExtraZ = sfmap (unsafeCoerce (\_ _ -> sFmapCart2D)) qfloor
                   (mult (mutt_instance_Cart2D q_mult) (MkCart2D
                     (cast inject_Z_Q
                       (totalLength z_plus (myCarDimZ carGeo)))
                     (cast inject_Z_Q (width (myCarDimZ carGeo))))
                     (lend extra1))}
  in
  let {
   leftExtraZ = sfmap (unsafeCoerce (\_ _ -> sFmapCart2D)) qfloor
                  (mult (mutt_instance_Cart2D q_mult) (MkCart2D
                    (cast inject_Z_Q (totalLength z_plus (myCarDimZ carGeo)))
                    (cast inject_Z_Q (width (myCarDimZ carGeo))))
                    (lstart extra1))}
  in
  plus (llll8 z_plus) initb (Build_Line2D
    (negate (negate_instance_Cart2D z_negate) (unsafeCoerce leftExtraZ))
    (unsafeCoerce rightExtraZ))

animateSpaceReq :: (CarGeometry Prelude.Integer) -> (([])
                   ((,) (Data.Ratio.Ratio Prelude.Integer)
                   (Data.Ratio.Ratio Prelude.Integer))) -> (BoundingRectangle
                   (Data.Ratio.Ratio Prelude.Integer)) -> Prelude.Integer ->
                   Prelude.String
animateSpaceReq carGeo moves0 extraSpace framesPerMove =
  let {sidewaysMove = map (mkNamedRelativeMove carGeo) moves0} in
  let {initStp = (,) (mkRenderingInfo ((,) ([]) ([]))) initSt} in
  let {cs = finerMovesStates framesPerMove sidewaysMove initStp} in
  let {namedLines = carStatesFrames carGeo cs} in
  let {
   boundRects = map
                  (compose (computeBoundingRectLines minClassZ maxClassZ z_0)
                    snd) namedLines}
  in
  let {
   boundRectsCum = fold_left_inter (boundingUnion minClassZ maxClassZ)
                     boundRects (zero (llll6 z_0))}
  in
  let {lineRects = zip namedLines boundRectsCum} in
  case lineRects of {
   ([]) -> ([]);
   (:) p _ ->
    case p of {
     (,) h _ ->
      let {initb = computeBoundingRectLines minClassZ maxClassZ z_0 (snd h)}
      in
      let {globalB = relGlobalBound carGeo initb extraSpace} in
      case drawEnv carGeo globalB initb of {
       (,) pp textPos0 ->
        let {
         textTikZ = \label ->
          append ((:) '\\' ((:) 'n' ((:) 'o' ((:) 'd' ((:) 'e' ((:) '[' ((:)
            'b' ((:) 'e' ((:) 'l' ((:) 'o' ((:) 'w' ((:) ' ' ((:) 'r' ((:)
            'i' ((:) 'g' ((:) 'h' ((:) 't' ((:) ']' ((:) ' ' ((:) 'a' ((:)
            't' ((:) ' ' ([])))))))))))))))))))))))
            (append (tikZPoint textPos0)
              (append ((:) '{' ([]))
                (append label
                  (append ((:) '}' ((:) ';' ([]))) newLineString))))}
        in
        let {
         frames = map (\p0 ->
                    let {bnd = snd p0} in
                    let {p1 = fst p0} in
                    let {
                     preface = sconcat ((:) pp ((:)
                                 (tikZFilledRect ((:) 'g' ((:) 'r' ((:) 'e'
                                   ((:) 'e' ((:) 'n' ([])))))) bnd) ([])))}
                    in
                    frameWithLines
                      (sconcat ((:) preface ((:) (textTikZ (fst (fst p1)))
                        ((:) (snd (fst p1)) ([]))))) (snd p1)) lineRects}
        in
        sconcat frames}}}

{-- extra space towards the (left, bottom) and  (right,top) --}
extra :: BoundingRectangle (Data.Ratio.Ratio Prelude.Integer)
extra = Build_Line2D (MkCart2D 0.2 0.1) (MkCart2D 0.2 1)

{-- Each pair corresponds to a move. The first component is the fixed turn curvature during the move.
1 denotes the maximum curvature for the car. So this value should be between 1 (max left-steered) and -1 (max right-steered).
0 means steered perfectly straight.
The second component denotes the signed distance covered (integral of linVel), as a fraction of the width of the car. 
So 1 means covering a distance equal to the width of the car  --}
moves :: ([])
         ((,) (Data.Ratio.Ratio Prelude.Integer)
         (Data.Ratio.Ratio Prelude.Integer))
moves = [(1,1), (-1,1)]

toPrint :: Prelude.String
toPrint =
  animateSpaceReq mazda3Sedan2014sGT moves extra ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x) 1))

main :: GHC.Base.IO ()
main = Prelude.putStrLn toPrint
