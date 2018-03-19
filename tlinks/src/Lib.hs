{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Lib where

import Bound ((>>>=), Var(B,F))
import Bound.Scope.Simple
-- import Bound.Scope
import Common
import Control.Exception (assert)
import Control.Monad (ap)
import Control.Monad.Morph (lift, hoist)
import Data.List (all)
import Data.Bifunctor (Bifunctor, first, second)
import Data.Functor.Classes (Eq1, liftEq)
import Data.Deriving (deriveShow1, deriveEq1, makeLiftEq)
import qualified Debug.Trace as Debug
import Text.PrettyPrint.ANSI.Leijen hiding (string, nest, (<$>), int)
import qualified Text.PrettyPrint.ANSI.Leijen as P
import GHC.Stack (HasCallStack)
import Type (Type, Kind)
import qualified Type as T
import qualified Hedgehog as H
import           Hedgehog hiding (Var, assert)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

mapSnd :: (Bifunctor p, Functor f) =>
  (b -> c) -> f (p a b) -> f (p a c)
mapSnd f = fmap (second f)

tvars, evars :: [String]
tvars = ["α", "β", "γ"] <> [ "α" <> show x | x <- [0 :: Integer ..] ]
evars = ["x", "y", "z"] <> [ "x" <> show x | x <- [0 :: Integer ..] ]

data Trace c
  = TrLit
  | TrIf
  | TrFor c
  | TrRow
  | TrEq c
  deriving (Eq, Functor)

data Const
  = Bool Bool
  | Int Int
  | String String
  deriving (Show, Eq)

data Expr c a x
  = Bottom
  | Const Const
  | Var x
  | If (Expr c a x) (Expr c a x) (Expr c a x)
  | Lam (c a) (Scope () (Expr c a) x)
  | Fix (c a) (Scope () (Expr c a) x)
  | (Expr c a x) :$ (Expr c a x)
  | TLam Kind (Expr (Scope () c) a x)
  | (Expr c a x) :§ (c a)
  | Empty (c a)
  | Singleton (Expr c a x)
  | Concat (Expr c a x) (Expr c a x)
  -- (c a) is the type of ELEMENTS of the first Expr argument
  | For (c a) (Expr c a x) (Scope () (Expr c a) x)
  | Record [(Label, Expr c a x)]
  -- The Type is the type of the record
  | Rmap (Expr c a x) (c a) (Expr c a x)
  -- the Type is the type of the record. I need this for tracing.
  | Proj Label (Expr c a x)
  | Table String (c a) -- type of ELEMENTS/ROWS that is, a record type, not a list type
  | Eq (c a) (Expr c a x) (Expr c a x) -- equality specialized to a type
  | Typecase (c a) (Expr c a x) (Expr c a x) (Expr c a x) (Expr (Scope () c) a x) (Expr (Scope () c) a x) (Expr (Scope () c) a x)
  | Trace (Trace (c a)) (Expr c a x)
  | Tracecase (Expr c a x) -- discriminant
               (Scope () (Expr c a) x) -- Lit
               (Scope () (Expr c a) x) -- If
               (Scope () (Expr (Scope () c) a) x) -- For
               (Scope () (Expr c a) x) -- Row
               (Scope () (Expr (Scope () c) a) x) -- Eq
  | Expr c a x ::: c a
  deriving (Functor)

-- deriveEq1 ''Expr
-- a = $(makeLiftEq ''Expr)

instance (Eq a, Monad c) => Applicative (Expr c a) where
  pure = return
  (<*>) = ap

instance (Eq a, Monad c) => Monad (Expr c a) where
  return = Var

  Bottom >>= _ = Bottom
  Const c >>= _ = Const c
  Var x >>= f = f x
  Fix t b >>= f = Fix t (b >>>= f)
  Lam t b >>= f = Lam t (b >>>= f)
  For t e b >>= f = For t (e >>= f) (b >>>= f)
  (:$) l r >>= f = (:$) (l >>= f) (r >>= f)
  TLam k b >>= f = TLam k (b >>= liftCE . f)
  (:§) e c >>= f = (:§) (e >>= f) c
  Empty t >>= _ = Empty t
  Singleton a >>= f = Singleton (a >>= f)
  Concat a b >>= f = Concat (a >>= f) (b >>= f)
  Record le >>= f = Record (map (\(l, x) -> (l, x >>= f)) le)
  Rmap a t b >>= f = Rmap (a >>= f) t (b >>= f)
  If i t e >>= f = If (i >>= f) (t >>= f) (e >>= f)
  Proj l e >>= f = Proj l (e >>= f)
  Table n t >>= _ = Table n t
  Eq t l r >>= f = Eq t (l >>= f) (r >>= f)
  Typecase c b i s l r t >>= f = Typecase c (b >>= f) (i >>= f) (s >>= f) (l >>= liftCE . f) (r >>= liftCE . f) (t >>= liftCE . f)
  Tracecase x l i g r q >>= f =
    Tracecase (x >>= f) (l >>>= f) (i >>>= f) (g >>>= liftCE . f) (r >>>= f) (q >>>= liftCE . f)
  Trace tc e >>= f = Trace tc (e >>= f)
  e ::: t >>= f = (e >>= f) ::: t

liftCE :: Monad c => Expr c a b -> Expr (Scope () c) a b
liftCE Bottom = Bottom
liftCE (Const c) = (Const c)
liftCE (Var x) = Var x
liftCE (e ::: t) = liftCE e ::: lift t
liftCE (Fix t b) = Fix (lift t) (hoistScope liftCE b)
liftCE (Lam t b) = Lam (lift t) (hoistScope liftCE b)
liftCE (For t e b) = For (lift t) (liftCE e) (hoistScope liftCE b)
liftCE ((:$) l r) = (:$) (liftCE l) (liftCE r)
liftCE (TLam k b) = TLam k (liftCE b)
liftCE ((:§) e c) = (:§) (liftCE e) (lift c)
liftCE (Empty t) = Empty (lift t)
liftCE (Singleton e) = Singleton (liftCE e)
liftCE (Concat a b) = Concat (liftCE a) (liftCE b)
liftCE (If i t e) = If (liftCE i) (liftCE t) (liftCE e)
liftCE (Record l) = Record (mapSnd liftCE l)
liftCE (Rmap a t b) = Rmap (liftCE a) (lift t) (liftCE b)
liftCE (Proj l e) = Proj l (liftCE e)
liftCE (Table n t) = Table n (lift t)
liftCE (Eq t l r) = Eq (lift t) (liftCE l) (liftCE r)
liftCE (Typecase c b i s l r t) = Typecase (lift c) (liftCE b) (liftCE i) (liftCE s) (liftCE l) (liftCE r) (liftCE t)
liftCE (Tracecase x l i f r oe) = Tracecase
  (liftCE x)
  (hoistScope liftCE l)
  (hoistScope liftCE i)
  (hoistScope liftCE f)
  (hoistScope liftCE r)
  (hoistScope liftCE oe)
liftCE (Trace tr e) = Trace (fmap lift tr) (liftCE e)

lam :: Eq x => x -> c a -> Expr c a x -> Expr c a x
lam x t b = Lam t (abstract1 x b)

for :: Eq x => x -> c a -> Expr c a x -> Expr c a x -> Expr c a x
for x t i o = For t i (abstract1 x o)

-- instantiate a constructor in an expression
eInstantiateC1 :: Eq a => Monad c => c a -> Expr (Scope () c) a x -> Expr c a x
eInstantiateC1 _ Bottom = Bottom
eInstantiateC1 _ (Const c) = Const c
eInstantiateC1 _ (Var x) = Var x
eInstantiateC1 a (e ::: t) = (eInstantiateC1 a e) ::: instantiate1 a t
eInstantiateC1 a (Lam t b) = Lam (instantiate1 a t) (hoistScope (eInstantiateC1 a) b)
eInstantiateC1 a (Fix t b) = Fix (instantiate1 a t) (hoistScope (eInstantiateC1 a) b)
eInstantiateC1 a ((:$) l r) = (:$) (eInstantiateC1 a l) (eInstantiateC1 a r)
eInstantiateC1 a (TLam k b) = TLam k (eInstantiateC1 (lift a) b)
eInstantiateC1 a ((:§) e c) = (:§) (eInstantiateC1 a e) (instantiate1 a c)
eInstantiateC1 a (Empty c) = Empty (instantiate1 a c)
eInstantiateC1 a (Singleton e) = Singleton (eInstantiateC1 a e)
eInstantiateC1 t (Concat a b) = Concat (eInstantiateC1 t a) (eInstantiateC1 t b)
eInstantiateC1 a (For t i o) = For (instantiate1 a t) (eInstantiateC1 a i) (hoistScope (eInstantiateC1 a) o)
eInstantiateC1 a (If c t e) = If (eInstantiateC1 a c) (eInstantiateC1 a t) (eInstantiateC1 a e)
eInstantiateC1 a (Record l) = Record (mapSnd (eInstantiateC1 a) l)
eInstantiateC1 a (Rmap x t y) = Rmap (eInstantiateC1 a x) (instantiate1 a t) (eInstantiateC1 a y)
eInstantiateC1 a (Proj l e) = Proj l (eInstantiateC1 a e)
eInstantiateC1 a (Table n t) = Table n (instantiate1 a t)
eInstantiateC1 a (Eq t l r) = Eq (instantiate1 a t) (eInstantiateC1 a l) (eInstantiateC1 a r)
eInstantiateC1 a (Typecase c b i s l r t) = Typecase (instantiate1 a c) (eInstantiateC1 a b) (eInstantiateC1 a i) (eInstantiateC1 a s) (eInstantiateC1 (lift a) l) (eInstantiateC1 (lift a) r) (eInstantiateC1 (lift a) t)
eInstantiateC1 a (Tracecase x l i f r oe) = Tracecase
  (eInstantiateC1 a x)
  (hoistScope (eInstantiateC1 a) l)
  (hoistScope (eInstantiateC1 a) i)
  (hoistScope (eInstantiateC1 (lift a)) f)
  (hoistScope (eInstantiateC1 a) r)
  (hoistScope (eInstantiateC1 (lift a)) oe)
eInstantiateC1 a (Trace tr e) = Trace (fmap (instantiate1 a) tr) (eInstantiateC1 a e)

-- abstract over a constructor in an expression
eAbstractC1 :: Eq a => Functor c => a -> Expr c a x -> Expr (Scope () c) a x
eAbstractC1 _ Bottom = Bottom
eAbstractC1 _ (Const c) = Const c
eAbstractC1 _ (Var x) = Var x
eAbstractC1 a (Lam t b) = Lam (abstract1 a t) (hoistScope (eAbstractC1 a) b)
eAbstractC1 a (Fix t b) = Fix (abstract1 a t) (hoistScope (eAbstractC1 a) b)
eAbstractC1 a ((:$) l r) = (:$) (eAbstractC1 a l) (eAbstractC1 a r)
eAbstractC1 a (TLam k b) = TLam k (eAbstractC1 a b)
eAbstractC1 a ((:§) e c) = (:§) (eAbstractC1 a e) (abstract1 a c)
eAbstractC1 a (Empty c) = Empty (abstract1 a c)
eAbstractC1 a (Singleton e) = Singleton (eAbstractC1 a e)
eAbstractC1 t (Concat a b) = Concat (eAbstractC1 t a) (eAbstractC1 t b)
eAbstractC1 a (For t i o) = For (abstract1 a t) (eAbstractC1 a i) (hoistScope (eAbstractC1 a) o)
eAbstractC1 a (If c t e) = If (eAbstractC1 a c) (eAbstractC1 a t) (eAbstractC1 a e)
eAbstractC1 a (Record l) = Record (mapSnd (eAbstractC1 a) l)
eAbstractC1 a (Rmap f t r) = Rmap (eAbstractC1 a f) (abstract1 a t) (eAbstractC1 a r)
eAbstractC1 a (Proj l r) = Proj l (eAbstractC1 a r)
eAbstractC1 a (Table n t) = Table n (abstract1 a t) -- not needed I think, should be base types..
eAbstractC1 a (Eq t l r) = Eq (abstract1 a t) (eAbstractC1 a l) (eAbstractC1 a r)
eAbstractC1 a (Typecase c b i s l r t) = Typecase (abstract1 a c) (eAbstractC1 a b) (eAbstractC1 a i) (eAbstractC1 a s) (eAbstractC1 a l) (eAbstractC1 a r) (eAbstractC1 a t)
eAbstractC1 a (Trace tr e) = Trace (fmap (abstract1 a) tr) (eAbstractC1 a e)


tlam :: Eq a => Monad c => a -> Kind -> Expr c a x -> Expr c a x
tlam a k b = TLam k (eAbstractC1 a b) -- this should be actual abstract, not my misnamed one, I think

-- the value trace analysis function
value :: Eq a => Expr Type a x
value = Fix (T.Forall T.KType (toScope (T.Arrow
                                      (T.Var (B ()))
                                      (T.App T.valuetf (T.Var (B ())))))) $ toScope $ TLam T.KType $ Typecase (toScope (T.Var (B ())))
        -- Bool
        (Lam (lift T.Bool) (toScope (Var (B ()))))
        -- Int
        (Lam (lift T.Int) (toScope (Var (B ()))))
        -- String
        (Lam (lift T.String) (toScope (Var (B ()))))
        -- Concat
        (Lam (lift (toScope (T.List (T.Var (B ())))))
          (toScope (For (toScope (toScope (T.Var (B ()))))
                     (Var (B ()))
                     (toScope (Singleton ((:$) ((:§) (Var (F (F (B ())))) (toScope (toScope (T.Var (B ()))))) (Var (B ()))))))))
        -- Record
        (Lam (toScope (toScope (T.Record (T.Var (B ())))))
          (toScope (Rmap (Var (F (B ()))) (toScope (toScope (T.Record (T.Var (B ()))))) (Var (B ())))))
        -- Trace
        (Lam (toScope (toScope (T.Trace (T.Var (B ())))))
         (toScope (Tracecase (Var (B ()))
                   -- Lit
                   (toScope (Var (B ())))
                   -- If
                   (toScope ((:$) ((:§) (Var (F (F (B ())))) (toScope (toScope (T.Trace (T.Var (B ()))))))
                              (Proj "out" (Var (B ())))))
                   -- For
                   (toScope ((:$) ((:§) (Var (F (F (B ())))) (toScope (toScope (toScope (T.Trace (T.Var (F (B ()))))))))
                             (Proj "out" (Var (B ())))))
                   -- Row
                   (toScope (Proj "data" (Var (B ()))))
                   -- OpEq
                   (toScope (Eq (toScope (toScope (toScope (T.Var (B ())))))
                             ((:$) ((:§) (Var (F (F (B ())))) (toScope (toScope (toScope (T.Trace (T.Var (B ())))))))
                               (Proj "left" (Var (B ()))))
                             ((:$) ((:§) (Var (F (F (B ())))) (toScope (toScope (toScope (T.Trace (T.Var (B ())))))))
                               (Proj "right" (Var (B ()))))))
                   )))

traceId :: Expr Type a x
traceId = TLam T.KType $ Lam (toScope (T.App (F <$> T.tracetf) (T.Var (B ())))) $ toScope (Var (B ()))

isApp :: Expr c a x -> Bool
isApp ((:$) _ _) = True
isApp ((:§) _ _) = True
isApp _ = False

prettyExpr :: ([String], [String]) -> Bool -> Expr Type String String -> Doc
prettyExpr ([], _) _ _ = error "ran out of variable names"
prettyExpr (_, []) _ _ = error "ran out of type variable names"
prettyExpr _ _ Bottom = red (char '⊥')
prettyExpr _ _ (Const (Bool b)) = text (show b)
prettyExpr _ _ (Const (Int b)) = text (show b)
prettyExpr _ _ (Const (String b)) = dquotes $ text b
prettyExpr _ _ (Var x) = text x
prettyExpr (vs, tvs) p (e ::: t) = pparens p $ prettyExpr (vs, tvs) True e <+> char ':' <+> T.prettyType tvs True t
prettyExpr (v:vs, tvs) p (Fix t e) = pparens p $ hang 2 $ group $
  bold (text "fix") <+> (text v <> colon <> T.prettyType tvs False t) <> dot P.<$$> prettyExpr (vs, tvs) False (instantiate1 (Var v) e)
prettyExpr (v:vs, tvs) p (Lam t b) = pparens p $ hang 2 $ group $
  bold (char 'λ') <> text v <> typeAnnotation <> char '.' P.<$$> prettyExpr (vs, tvs) False (instantiate1 (Var v) b)
  where typeAnnotation = char ':' <> T.prettyType tvs False t
prettyExpr (vs, tv:tvs) p (TLam k b) = pparens p $ hang 2 $ group $
  bold (char 'Λ') <> text tv <> kindAnnotation <> char '.' P.<$$> prettyExpr (vs, tvs) False (eInstantiateC1 (T.Var tv) b)
  where kindAnnotation = case k of
          T.KType -> empty
          _ -> char ':' <> T.prettyKind k
prettyExpr ns p ((:$) l r) = pparens p $ hang 2 $
  prettyExpr ns (not $ isApp l) l P.<$> prettyExpr ns True r
prettyExpr (vs, tvs) p ((:§) e c) = pparens p $
  prettyExpr (vs, tvs) (not $ isApp e) e </> T.prettyType tvs True c
prettyExpr (_,_tvs) _ (Empty _t) = brackets empty -- (T.prettyType tvs False t)
prettyExpr ns _ (Singleton e) = brackets (prettyExpr ns False e)
prettyExpr ns p (Concat a b) = pparens p $ prettyExpr ns True a <+> text "++" <+> prettyExpr ns True b
prettyExpr ns p (Eq _t l r) = pparens p $ prettyExpr ns True l <+> text "==" <+> prettyExpr ns True r
prettyExpr (v:vs, tvs) p (For t i o) = pparens p $ hang 2 $
  bold (text "for") <+> (hang 3 (parens (text v <> typeAnnotation <+> text "<-" <+> prettyExpr (v:vs, tvs) False i))) P.<$> prettyExpr (vs, tvs) False (instantiate1 (Var v) o)
  where typeAnnotation = char ':' <+> T.prettyType tvs False t
prettyExpr _ _ (Record []) = braces empty
prettyExpr ns _ (Record l) = group $ braces $ align (cat (punctuate (comma <> space) (map (\(lbl, e) -> blue (text lbl) <+> char '=' <+> prettyExpr ns False e) l)))
prettyExpr ns p (If c t e) = pparens p $ group $ align $
  bold (text "if") <+> prettyExpr ns True c P.<$>
  bold (text "then") <+> prettyExpr ns True t P.<$>
  bold (text "else") <+> prettyExpr ns True e
prettyExpr ns _ (Proj l e) = --pparens p $
  prettyExpr ns True e <> char '.' <> blue (text l)
prettyExpr (_, tvs) p (Table n t) = pparens p $
  bold (text "table") <+> text (show n) <+> T.prettyType tvs True t
prettyExpr (ns, tv:tvs) p (Typecase c b i s l r t) = pparens p $
  bold (text "typecase") <+> T.prettyType (tv:tvs) False c <+> bold (text "of") <$$>
  (indent 2 $
    text "Bool => " <> prettyExpr (ns, tv:tvs) False b <$$>
    text "Int => " <> prettyExpr (ns, tv:tvs) False i <$$>
    text "String => " <> prettyExpr (ns, tv:tvs) False s <$$>
    text "List " <> text tv <> text " => " <> prettyExpr (ns, tvs) False (eInstantiateC1 (T.Var tv) l) <$$>
    text "Record " <> text tv <> text " => " <> prettyExpr (ns, tvs) False (eInstantiateC1 (T.Var tv) r) <$$>
    text "Trace " <> text tv <> text " => " <> prettyExpr (ns, tvs) False (eInstantiateC1 (T.Var tv) t))
prettyExpr ns p (Rmap f _t r) = pparens p $
  bold (text "rmap") <+> prettyExpr ns True f <+> prettyExpr ns True r
prettyExpr (v:vs, tv:tvs) p (Tracecase x l i f r oe) = pparens p $
  bold (text "tracecase") <+> prettyExpr (v:vs, tv:tvs) False x <+> bold (text "of") <$$>
  (indent 2 $
    text "Lit" <+> text v <+> text "=>" <+> prettyExpr (vs, tv:tvs) False (instantiate1 (Var v) l) <$$>
    text "If" <+> text v <+> text "=>" <+> prettyExpr (vs, tv:tvs) False (instantiate1 (Var v) i) <$$>
    text "For" <+> text tv <+> text v <+> text "=>" <+> prettyExpr (vs, tvs) False (eInstantiateC1 (T.Var tv) (instantiate1 (Var v) f)) <$$>
    text "Row" <+> text v <+> text "=>" <+> prettyExpr (vs, tv:tvs) False (instantiate1 (Var v) r) <$$>
    text "Op==" <+> text tv <+> text v <+> text "=>" <+> prettyExpr (vs, tvs) False (eInstantiateC1 (T.Var tv) (instantiate1 (Var v) oe)))
prettyExpr ns p (Trace TrLit e) = pparens p $ green (text "Lit") <+> prettyExpr ns True e
prettyExpr ns p (Trace TrRow e) = pparens p $ green (text "Row") <+> prettyExpr ns True e
prettyExpr ns p (Trace TrIf e) = pparens p $ green (text "If") <+> prettyExpr ns True e
prettyExpr ns@(_, tvs) p (Trace (TrFor c) e) = pparens p $ green (text "For") <+> {- T.prettyType tvs True c <+> -} prettyExpr ns True e
prettyExpr ns@(_, tvs) p (Trace (TrEq c) e) = pparens p $ green (text "Eq") <+> {- prettyType tvs True c <+> -} prettyExpr ns True e

instance Show (Expr Type String String) where
  showsPrec _ e = displayS (renderPretty 0.6 90 (prettyExpr (evars, tvars) False e))

unroll :: Eq a => Monad c => Int -> Expr c a x -> Expr c a x
unroll 0 (Fix _ _) = Bottom
unroll n (Fix t b) = unroll (n-1) (instantiate1 (Fix t b) b)
unroll _ Bottom = Bottom
unroll _ (Const c) = Const c
unroll _ (Var x) = Var x
unroll n (If c t e) = If (unroll n c) (unroll n t) (unroll n e)
unroll n (Lam t b) = Lam t (hoistScope (unroll n) b)
unroll n ((:$) a b) = (:$) (unroll n a) (unroll n b)
unroll n (TLam k b) = TLam k (unroll n b)
unroll n ((:§) e c) = (:§) (unroll n e) c
unroll _ (Empty t) = Empty t
unroll n (Singleton e) = Singleton (unroll n e)
unroll n (Concat a b) = Concat (unroll n a) (unroll n b)
unroll n (For t i o) = For t (unroll n i) (hoistScope (unroll n) o)
unroll n (Record l) = Record (mapSnd (unroll n) l)
unroll n (Proj l e) = Proj l (unroll n e)
unroll _ (Table name t) = Table name t
unroll n (Rmap a t b) = Rmap (unroll n a) t (unroll n b)
unroll n (Eq t l r) = Eq t (unroll n l) (unroll n r)
unroll n (Typecase c b i s l r t) = Typecase c (unroll n b) (unroll n i) (unroll n s) (unroll n l) (unroll n r) (unroll n t)
unroll n (Tracecase x l i f r oe) = Tracecase
  (unroll n x)
  (hoistScope (unroll n) l)
  (hoistScope (unroll n) i)
  (hoistScope (unroll n) f)
  (hoistScope (unroll n) r)
  (hoistScope (unroll n) oe)
unroll n (Trace tr e) = Trace tr (unroll n e)
unroll n (e ::: t) = (unroll n e) ::: t

one :: Show x => Show a => Eq a => Expr Type a x -> Expr Type a x
one Bottom = Bottom
one (Const c) = Const c
one (Var v) = Var v
one (If (Const (Bool True)) t _) = t
one (If (Const (Bool False)) _ e) = e
one (If c t e) = If (one c) (one t) (one e)
one ((:$) (Lam _ b) a) = instantiate1 a b
one ((:$) a b) = (:$) (one a) b
-- one (E(:$) a b) = E(:$) (one a) (one b) -- one b is not necessary, but helps finding bugs
-- one (Lam t b) = Lam t (hoistScope one b) -- for debugging only
one l@Lam{} = l -- do not normalize under lambda
one (Fix _ _) = error "Unexpected fix"
one (TLam _ _) = error "TODO Lambda"
one ((:§) (TLam _ b) c) = eInstantiateC1 c b
one ((:§) a c) = (:§) (one a) c
one (Table n t) = Table n t
one (Empty t) = Empty t
one (Singleton e) = Singleton (one e)
one (Concat (Empty _) r) = r
one (Concat l (Empty _)) = l
one (Concat l r) = Concat (one l) (one r)
one f@(For _ (Empty _) _) = Empty (elementType (typeof f))
  where elementType (T.List et) = et
        elementType _ = error "not a list type"
one (For _ (Singleton e) o) = instantiate1 e o
one (For it (Concat l r) o) = (For it l o) `Concat` (For it r o)
one (For it (If c t e) o) = If c (For it t o) (For it e o)
-- for (x <- for (y <- L) M) N ~> for (y <- L) (for (x <- M) N)
-- This circumvents the safety implied by the Scope scope safety, but
-- should be correct. Variables in L stay unchanged. y is visible in
-- M, bound by the preceding for. The nesting looks different in
-- source code, but the binding structure is the same. On the left
-- side, x is visible in N, bound by the outer for. On the right side,
-- x is visible in N, bound by the outer for, so that stays the same.
-- On the right side, y is visible in N, but not used. However, all
-- other free variables need to move up one binder to account for y.
one (For xt (For yt l (Scope m)) n) =
  For yt l (Scope (For xt m (F <$> n)))
-- no, no, need proper elim frames
-- one (EFor t (EVar x) o) = EFor t (EVar x) (hoistScope one o) -- for debugging only

-- without eta expansion of tables:
one (For t (Table n tt) o) = For t (Table n tt) (hoistScope one o)
-- -- with eta expansion of tables:
-- one (For t (Table n tt@(TT (CRecord row))) o) = For t (Table n tt) etaO --(hoistScope one o)
  -- where
    -- etaO :: Scope () (Expr Type a) x
    -- etaO = Scope (splat (pure . F) (const (ERecord (map (\(l, _) -> (l, EProj l tt (EVar (B ())))) (rowToList row)))) o)
one (For t i o) = For t (one i) o --(hoistScope one o)
one (Record fs) = Record (mapSnd one fs)
one (Rmap f (T.Record row) r) = Record
  (map (\(l,t) -> (l, f :§ t :$ Proj l r))
    (T.rowToList row))
one (Rmap _ _ _) = error "TODO need to normalize type (and switch to constructor, not type to begin with, I think"
one (Proj l (Record fs)) = case lookup l fs of
  Nothing -> error "label not found in record"
  Just e -> e
one (Proj l e) = Proj l (one e)
-- one (EEq _ l r) | l == r = ETrue --
one (Eq t l r) = Eq t (one l) (one r)
one (Typecase c b i s l r t) = case c of
  T.Bool -> b; T.Int -> i; T.String -> s;
  T.List c' -> eInstantiateC1 c' l
  T.Record c' -> eInstantiateC1 c' r
  T.Trace c' -> eInstantiateC1 c' t
  _ -> Typecase (T.norm c) b i s l r t
one (Tracecase x l i f r oe) = case x of
  Trace tr t -> instantiate1 t (case tr of
                                   TrLit -> l; TrIf -> i; TrRow -> r
                                   TrFor c -> hoistScope (eInstantiateC1 c) f
                                   TrEq c -> hoistScope (eInstantiateC1 c) oe)
  x' -> Tracecase (one x') l i f r oe
one (Trace tr e) = Trace tr (one e)
one (e ::: t) = one e ::: t

tid :: Eq a => Monad c => Scope () (Expr c a) x
tid = toScope (Var (B ()))

trace :: HasCallStack => Show x => Eq a => Expr Type a x -> Expr Type a x
trace (Var x) = error "Unannotated variables shouldn't happen, right?" -- Var x
trace (Var x ::: t) = Var x -- ::: t
trace (Const c) = Trace TrLit (Const c)
trace (If c t e) =
  If (value :§ T.Trace T.Bool :$ trace c)
  ((distTRACE (toScope (Trace TrIf (Record [("cond", F <$> trace c), ("out", Var (B ()))]))) (typeof t)) :$ trace t)
  ((distTRACE (toScope (Trace TrIf (Record [("cond", F <$> trace c), ("out", Var (B ()))]))) (typeof e)) :$ trace e)
trace (Empty c) = Empty (T.App T.tracetf c)
trace (Singleton e) = Singleton (trace e)
trace (Concat l r) = Concat (trace l) (trace r)
trace (For it ie o) =
  For (T.App T.tracetf it) (trace ie)
      (toScope (distTRACE (toScope (Trace (TrFor (T.App T.tracetf it))
                                    (Record [("in", Var (F (B ()))), ("out", Var (B ()))])))
                 (typeof (instantiate1 (Bottom ::: it) o))
                 :$ trace (fromScope o)))
trace (Record fields) = Record (second trace <$> fields)
trace (Proj l r) = Proj l (trace r)
trace (Table n (T.Record row)) = For (T.Record row) (Table n (T.Record row))
  (toScope (Singleton (Record (map (\(l,_) -> (l, tblTrace l)) (T.rowToList row)))))
  where tblTrace l = Trace TrRow (Record [("table", Const (String n)),
                                          ("column", Const (String l)),
                                          ("data", Proj l (Var (B ())))])
trace (Eq t l r) = Trace (TrEq (T.App T.tracetf t)) (Record [("left", trace l), ("right", trace r)])

-- Calls dist, but applies the TRACE type function to the type argument first
distTRACE k t = dist k (T.norm (T.App T.tracetf t))

dist :: forall a x. Scope () (Expr Type a) x -> Type a -> Expr Type a x
dist k T.Bool = Lam T.Bool k -- these shouldn't happen, right?
dist k T.Int = Lam T.Int k
dist k T.String = Lam T.String k
dist k (T.List t) = Lam (T.List t) (toScope (For t (Var (B ())) (toScope (Singleton ((F . F <$> dist k t) :$ (Var (B ())))))))
dist k (T.Record row) = Lam (T.Record row) (toScope (Record (map field (T.rowToList row))))
  where
    field :: (Label, Type a) -> (Label, Expr Type a (Var () x))
    field (l, t) = (l, (F <$> dist k t) :$ (Proj l (Var (B ()))))
dist k (T.Trace t) = Lam (T.Trace t) k

-- Ugh. I might need an actual typechecker...
typeof :: HasCallStack => Show x => Eq a => Expr Type a x -> Type a
typeof Bottom = error "bottom"
typeof (Var x) = error $ "unannotated var " ++ show x
typeof (Const (Bool _)) = T.Bool
typeof (Const (Int _)) = T.Int
typeof (Const (String _)) = T.String
typeof (Bottom ::: t) = t
typeof (Var _ ::: t) = t
typeof (e ::: t) = assert (typeof e == t) t
typeof (Record fs) = T.Record (rowType fs)
  where rowType [] = T.RowNil
        rowType ((l,e):es) = T.RowCons l (typeof e) (rowType es)
typeof (Singleton e) = T.List (typeof e)
typeof (Proj l e) = case typeof e of
  T.Record row -> case lookup l (T.rowToList row) of
    Nothing -> error "Label not found in record"
    Just t -> t
  _ -> error "Not a record type in projection"
typeof (If c t e) =
  -- assert (typeof c == T.Bool) $
  -- assert (typeof t == typeof e) $
  typeof t
typeof (Empty c) = T.List c
typeof (Concat l r) =
  -- assert (typeof l == typeof r) $
  typeof l
typeof (f :$ a) = case typeof f of
  T.Arrow ta tb -> {- assert (ta == typeof a) $ -} tb
  _ -> error "not a function type"
typeof (Lam a b)  = T.Arrow a (typeof (instantiate1 (Bottom ::: a) b))
typeof (Fix t b) = typeof (instantiate1 (Bottom ::: t) b)
typeof (TLam k b) =
  let t = typeof (eInstantiateC1 (T.Var undefined) b)
  in T.Forall k (toScope (F <$> t))
typeof ((TLam k b) :§ t) = typeof (eInstantiateC1 t b)
 -- this is not right, should check function to T.Forall, like :$
typeof (f :§ t) = case T.norm (typeof f) of
  T.Lam k b -> error "type lam"
  T.Forall k b -> instantiate1 t b
typeof (Trace TrLit c) = T.Trace (typeof c)
typeof (Trace TrIf i) = typeof (Proj "out" i)
typeof (Trace (TrFor _) i) = typeof (Proj "out" i)
typeof (Trace TrRow r) = T.Trace (typeof (Proj "data" r))
typeof (Trace (TrEq _) r) = T.Trace T.Bool
typeof (For t i o) =
  -- assert (typeof i == T.List t) $
  typeof (instantiate1 (Bottom ::: t) o)
typeof (Table _ (T.Record row)) =
  assert (all (T.isBaseType . snd) (T.rowToList row)) $
  T.List (T.Record row)
typeof (Table _ _) = error "nonrecord table type"
typeof (Rmap _ _ _) = error "todo"
typeof (Eq _ _ _) = T.Bool
typeof (Typecase x b i s l r t) = case T.norm x of
  T.Bool -> typeof b
  T.Int -> typeof i
  T.String -> typeof s
  T.List et -> typeof (eInstantiateC1 et l)
  T.Record row -> typeof (eInstantiateC1 row r)
  T.Trace et -> typeof (eInstantiateC1 et t)
  T.Var _ -> error "uh, dunno"
typeof Tracecase{} = error "tracecase"

putE :: Expr Type String String -> IO ()
putE e = do
  putDoc $ prettyExpr (evars, tvars) False e
  putStrLn ""

putC :: Type String -> IO ()
putC c = do
  putDoc $ T.prettyType tvars False c
  putStrLn ""

showTraced :: Expr Type String String -> IO ()
showTraced e = do
  putStrLn "===================="
  putE e
  putStrLn "-------trace---->"
  putE $
    (!! 145) . iterate one $ unroll 3 $
    trace e

true, false :: Expr c a x
true = Const (Bool True)
false = Const (Bool False)

int :: Int -> Expr c a x
int = Const . Int
string :: String -> Expr c a x
string = Const . String

genIf :: Show x => Show a => Eq a => [(x, Type a)] -> Type a -> Gen (Expr Type a x)
genIf env ty = do
  c <- genTypedExpr env T.Bool
  Gen.subtermM2
    (genTypedExpr env ty)
    (genTypedExpr env ty)
    (\t e -> pure (If c t e))

genFor :: Eq a => Show x => Show a => [(x, Type a)] -> Type a -> Gen (Expr Type a x)
genFor env et = do
  it <- T.genType
  ie <- genTypedExpr env (T.List it)
  oe <- genTypedExpr ((B (), it):(first F <$> env)) (T.List et)
  pure (For it ie (toScope oe))

boundVars :: HasCallStack => Eq a => Show a => Show x =>
  [(x, Type a)] -> Type a -> [ Gen (Expr Type a x) ]
boundVars env ty = [ pure (Var x) | (x,t) <- env, t == ty ]

genProj :: (Show a, Show x, Eq a) =>
  [(x, Type a)] -> Type a -> Gen (Expr Type a x)
genProj env ty = do
  (l:ls) <- T.genDistinctLabels
  row <- T.genRowFromLabels ls
  r <- genTypedExpr env (T.Record (T.RowCons l ty row))
  pure (Proj l r)

-- TODO this *very* rarely produces terms that use bound variables
-- (and never free variables, but that's good).
genTypedExpr :: HasCallStack => Eq a => Show x => Show a =>
  [(x, Type a)] -> Type a -> Gen (Expr Type a x)
genTypedExpr env ty = Gen.recursive Gen.choice
  (genBase ++ boundVars env ty)
  ([ genIf env ty, genProj env ty ] ++ genRec)
  where
    genBase = case ty of
      T.Bool -> [ pure true, pure false ]
      T.Int -> [ Gen.int (Range.constant 0 42) >>= (pure . int) ]
      T.String -> [ Gen.string (Range.constant 0 10) (Gen.unicode) >>= (pure . string) ]
      (T.List (T.Record row))
        | all (T.isBaseType . snd) (T.rowToList row) ->
          [ pure (Empty (T.Record row)),
            do name <- T.genLabel
               pure (Table name (T.Record row)) ]
      (T.List et) -> [ pure (Empty et) ]
      (T.Record row) -> [
        do
          fields <- traverse (\(l, t) ->
                                 genTypedExpr env t >>= pure . (l,))
                    (T.rowToList row)
          pure (Record fields)
        ]

    genRec = case ty of
      T.Bool -> [ do t <- T.genType
                     l <- genTypedExpr env t
                     r <- genTypedExpr env t
                     pure (Eq t l r)
                ]
      T.Int -> []
      T.String -> []
      (T.List et) ->
        [ genTypedExpr env et >>= pure . Singleton
        , Gen.subtermM2 (genTypedExpr env ty) (genTypedExpr env ty) (\l r -> pure (Concat l r))
        , genFor env et ]
      (T.Record _) -> []

prop_norm_preserve :: Property
prop_norm_preserve =
  property $ do
    t :: Type String <- forAll $ T.genType
    e :: Expr Type String String <- forAll $ genTypedExpr [] t
    n <- forAll $ Gen.int (Range.linear 0 100)
    norm <- eval $ (!! n) . iterate one $ e
    typeof norm === t

prop_genTypedExpr_typeof :: HasCallStack => Property
prop_genTypedExpr_typeof =
  property $ do
    t <- forAll $ T.genType
    e :: Expr Type String String <- forAll $ genTypedExpr [] t
    te <- eval (typeof e)
    te === t

-- This fails when the query expression uses variables, because they
-- are not type-annotated.
prop_trace_type :: Property
prop_trace_type = property $ do
  t <- forAll $ T.genType
  e :: Expr Type String String <- forAll $ genTypedExpr [] t
  tre <- eval $ (!! 100) . iterate one $ unroll 5 $ trace e
  tretype <- eval (T.norm (typeof tre))
  normt <- eval (T.norm (T.App T.tracetf t))
  tretype === normt

-- prop_trace_value_type :: Property
-- prop_trace_value_type = property $ do
  -- t <- forAll $ T.genType
  -- e :: Expr Type String String <- forAll $ genTypedExpr [] t
  -- val <- eval $ (!! 1000) . iterate one $ unroll 20 (value :§ (T.App T.tracetf t) :$ trace e)
  -- footnoteShow val
  -- typeof val === t

tests :: IO Bool
tests =
  checkParallel $ Group "group"
  [ ("genTypedExpr generates well-typed terms", prop_genTypedExpr_typeof)
  , ("one preserves types across iterations", prop_norm_preserve)
  , ("traced terms have TRACE type after some normalization", prop_trace_type)
  -- , ("`value` of traced terms has same type", prop_trace_value_type)
  ]

someFunc :: IO ()
someFunc = do

  showTraced $ Empty T.Bool
  showTraced $ Singleton true
  showTraced $ Singleton (Singleton true)
  showTraced $ Concat (Empty T.Bool) (Singleton true)
  showTraced $ If true false true
  showTraced $ If true (If false (string "then then") (string "then else"))
                       (If true (string "else then") (string "else else"))
  showTraced $ Concat (If true (Singleton true) (Empty T.Bool)) (Singleton false)
  showTraced $ If true (Concat (Singleton true) (Singleton false)) (Empty T.Bool)
  
  showTraced $ for "x" T.Bool (Singleton true) (Singleton true)
  showTraced $ for "x" (T.List T.Bool) (Singleton (Singleton true)) (If true ((Var "x") ::: (T.List T.Bool)) (Singleton false))

  
  let crab = T.Record (T.RowCons "a" T.String (T.RowCons "b" T.Bool T.RowNil))
  let tableABs = Table "abs" crab
  showTraced $ tableABs

  let xFromTable = for "x" crab tableABs (Singleton (Var "x" ::: crab))
  showTraced $ xFromTable
  let asFromTable = for "x" crab tableABs (Singleton (Proj "a" (Var "x" ::: crab)))
  showTraced $ asFromTable

  let bsFromTable = for "x" crab tableABs (Singleton (Proj "b" (Var "x" ::: crab)))
  showTraced $ for "y" T.Bool bsFromTable $ If (Var "y" ::: T.Bool) (Singleton (int 1)) (Empty T.Int)

  showTraced (Empty T.Bool)
  putE $ (!! 100) . iterate one $ unroll 5 $ value :§ T.App T.tracetf (T.List T.Bool) :$ trace (Empty T.Bool)

  -- putStrLn "------ random term -------"
  -- ty <- Gen.sample T.genType
  -- putC ty
  -- ex <- Gen.sample (genTypedExpr [] ty)
  -- putE ex
  -- let n = (!! 100) . iterate one $ ex
  -- putE $ n
  -- putC (typeof ex)
  -- putC (typeof n)

  res <- tests
  putStrLn (show res)
  -- putStrLn "------ another -------"
  -- t' <- Gen.sample T.genType
  -- putC t'
  -- Gen.sample (genTypedExpr [] t') >>= putE
