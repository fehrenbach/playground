{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns -Werror=incomplete-patterns #-}

module Ty where

import Supply (MonadSupply, fresh)

type V = Integer
type L = String

data Ty
  = V V
  | B | I | S
  | All V Ty
  | V :-> Ty
  | Ty :$ Ty
  | L Ty | R Ty
  | N | (L,Ty) :| Ty
  | T Ty
  | Rec Ty (Ty, Ty, Ty, Ty, Ty, Ty)
  deriving (Show)

subst :: Ty -> (V, Ty) -> Ty
subst (V v) (v', s) | v == v' = s
subst (V v) _ = V v
subst B _ = B
subst I _ = I
subst S _ = S
subst (All v t) s = All v (t `subst` s)
subst (x :-> t) s = x :-> (t `subst` s)
subst (a :$ b) s = (a `subst` s) :$ (b `subst` s)
subst (L t) s = L (t `subst` s)
subst (R t) s = R (t `subst` s)
subst N _ = N
subst ((l, t) :| r) s = (l, t `subst` s) :| (r `subst` s)
subst (T t) s = T (t `subst` s)
subst (Rec a (b, i, s, l, r, t)) su = Rec (a `subst` su)
  (b `subst` su,
   i `subst` su,
   s `subst` su,
   l `subst` su,
   r `subst` su,
   t `subst` su)

norm :: Ty -> Ty
norm (V v) = V v
norm B = B
norm I = I
norm S = S
norm N = N
norm ((l,t) :| r) = (l, norm t) :| norm r
norm ((x :-> b) :$ a) = norm (b `subst` (x,a))
norm (f :$ a) = norm $ norm f :$ a
norm (x :-> b) = x :-> norm  b
norm (R r) = R (norm r)
norm (L r) = L (norm r)
norm (T r) = T (norm r)
norm (Rec a cs@(b, i, s, l, r, t)) = norm $ case norm a of
  B -> b; I -> i; S -> s
  L x -> l :$ x :$ Rec x cs
  R x -> r :$ x :$ Rec x cs
  T x -> t :$ x :$ Rec x cs
  _ -> Rec a cs
norm (All x e) = All x (norm e)

ty = (122 :-> Rec (V 122) (T B,T I,T S,123 :-> (124 :-> L (V 124)),125 :-> (126 :-> R (V 126)),127 :-> (128 :-> T (V 128)))) :$ L B


tRACE :: MonadSupply V m => m Ty
tRACE = do
  a <- fresh
  l1 <- fresh
  l2 <- fresh
  r1 <- fresh
  r2 <- fresh
  t1 <- fresh
  t2 <- fresh
  pure (a :-> Rec (V a) (T B, T I, T S, l1 :-> (l2 :-> L (V l2)), r1 :-> (r2 :-> R (V r2)), t1 :-> (t2 :-> T (V t2))))

vALUE :: MonadSupply V m => m Ty
vALUE = do
  a <- fresh
  l1 <- fresh
  l2 <- fresh
  r1 <- fresh
  r2 <- fresh
  t1 <- fresh
  t2 <- fresh
  pure (a :-> Rec (V a) (B, I, S, l1 :-> (l2 :-> L (V l2)), r1 :-> (r2 :-> R (V r2)), t1 :-> (t2 :-> V t2)))
