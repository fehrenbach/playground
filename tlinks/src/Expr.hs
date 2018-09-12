{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Expr where

import Data.Bifunctor (Bifunctor, first, second)
import Bound ((>>>=), Var(B,F))
import Bound.Scope.Simple
import Type (Type, Kind)
import qualified Type as T
import Common
import Data.Monoid ((<>))
import Control.Monad (ap)
import Control.Monad.Morph (lift, hoist)
import Text.PrettyPrint.ANSI.Leijen hiding (string, nest, (<$>), int)
import qualified Text.PrettyPrint.ANSI.Leijen as P

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
  | TrAnd
  deriving (Eq, Functor)

data Const
  = Bottom
  | Bool Bool
  | Int Int
  | String String
  deriving (Show, Eq)

data Expr c a x
  = Const Const
  | Var x
  | If (Expr c a x) (Expr c a x) (Expr c a x)
  | Lam (c a) (Scope () (Expr c a) x)
  | Fix (c a) (Scope () (Expr c a) x)
  | (Expr c a x) :$ (Expr c a x)
  | TLam Kind (Expr (Scope () c) a x)
  | (Expr c a x) :§ (c a)
  | Empty (c a)
  | Singleton (Expr c a x)
  | Concat [Expr c a x]
  | For (Expr c a x) (Scope () (Expr c a) x)
  | Record [(Label, Expr c a x)]
  -- The Type is the type of the record
  | Rmap (Expr c a x) (c a) (Expr c a x)
  | Rfold (Expr c a x) (Expr c a x) (Expr c a x) (c a) -- function, init, record, record's type
  | Proj Label (Expr c a x)
  | Table String (c a) -- type of ELEMENTS/ROWS that is, a record type, not a list type
  | Eq (c a) (Expr c a x) (Expr c a x) -- equality specialized to a type
  | And (Expr c a x) (Expr c a x)
  | Typecase (c a) (Expr c a x) (Expr c a x) (Expr c a x) (Expr (Scope () c) a x) (Expr (Scope () c) a x) (Expr (Scope () c) a x)
  | Trace (Trace (c a)) (Expr c a x)
  | Tracecase (Expr c a x) -- discriminant
               (Scope () (Expr c a) x) -- Lit
               (Scope () (Expr c a) x) -- If
               (Scope () (Expr (Scope () c) a) x) -- For
               (Scope () (Expr c a) x) -- Row
               (Scope () (Expr (Scope () c) a) x) -- Eq
               (Scope () (Expr c a) x) -- And
  | Expr c a x ::: c a -- type ascription/annotation
  deriving (Functor)

-- deriveEq1 ''Expr
-- a = $(makeLiftEq ''Expr)

instance (Eq a, Monad c) => Applicative (Expr c a) where
  pure = return
  (<*>) = ap

instance (Eq a, Monad c) => Monad (Expr c a) where
  return = Var

  Const c >>= _ = Const c
  Var x >>= f = f x
  Fix t b >>= f = Fix t (b >>>= f)
  Lam t b >>= f = Lam t (b >>>= f)
  For e b >>= f = For (e >>= f) (b >>>= f)
  (:$) l r >>= f = (:$) (l >>= f) (r >>= f)
  TLam k b >>= f = TLam k (b >>= liftCE . f)
  (:§) e c >>= f = (:§) (e >>= f) c
  Empty t >>= _ = Empty t
  Singleton a >>= f = Singleton (a >>= f)
  Concat l >>= f = Concat (map (>>= f) l)
  Record le >>= f = Record (map (\(l, x) -> (l, x >>= f)) le)
  Rmap a t b >>= f = Rmap (a >>= f) t (b >>= f)
  Rfold l m n d >>= f = Rfold (l >>= f) (m >>= f) (n >>= f) d
  If i t e >>= f = If (i >>= f) (t >>= f) (e >>= f)
  Proj l e >>= f = Proj l (e >>= f)
  Table n t >>= _ = Table n t
  Eq t l r >>= f = Eq t (l >>= f) (r >>= f)
  And l r >>= f = And (l >>= f) (r >>= f)
  Typecase c b i s l r t >>= f = Typecase c (b >>= f) (i >>= f) (s >>= f) (l >>= liftCE . f) (r >>= liftCE . f) (t >>= liftCE . f)
  Tracecase x l i g r q a >>= f =
    Tracecase (x >>= f) (l >>>= f) (i >>>= f) (g >>>= liftCE . f) (r >>>= f) (q >>>= liftCE . f) (a >>>= f)
  Trace tc e >>= f = Trace tc (e >>= f)
  e ::: t >>= f = (e >>= f) ::: t

liftCE :: Monad c => Expr c a b -> Expr (Scope () c) a b
liftCE (Const c) = (Const c)
liftCE (Var x) = Var x
liftCE (e ::: t) = liftCE e ::: lift t
liftCE (Fix t b) = Fix (lift t) (hoistScope liftCE b)
liftCE (Lam t b) = Lam (lift t) (hoistScope liftCE b)
liftCE (For e b) = For (liftCE e) (hoistScope liftCE b)
liftCE ((:$) l r) = (:$) (liftCE l) (liftCE r)
liftCE (TLam k b) = TLam k (liftCE b)
liftCE ((:§) e c) = (:§) (liftCE e) (lift c)
liftCE (Empty t) = Empty (lift t)
liftCE (Singleton e) = Singleton (liftCE e)
liftCE (Concat l) = Concat (liftCE <$> l)
liftCE (If i t e) = If (liftCE i) (liftCE t) (liftCE e)
liftCE (Record l) = Record (mapSnd liftCE l)
liftCE (Rmap a t b) = Rmap (liftCE a) (lift t) (liftCE b)
liftCE (Rfold a b c t) = Rfold (liftCE a) (liftCE b) (liftCE c) (lift t)
liftCE (Proj l e) = Proj l (liftCE e)
liftCE (Table n t) = Table n (lift t)
liftCE (Eq t l r) = Eq (lift t) (liftCE l) (liftCE r)
liftCE (And l r) = And (liftCE l) (liftCE r)
liftCE (Typecase c b i s l r t) = Typecase (lift c) (liftCE b) (liftCE i) (liftCE s) (liftCE l) (liftCE r) (liftCE t)
liftCE (Tracecase x l i f r oe oa) = Tracecase
  (liftCE x)
  (hoistScope liftCE l)
  (hoistScope liftCE i)
  (hoistScope liftCE f)
  (hoistScope liftCE r)
  (hoistScope liftCE oe)
  (hoistScope liftCE oa)
liftCE (Trace tr e) = Trace (fmap lift tr) (liftCE e)

lam :: Eq x => x -> c a -> Expr c a x -> Expr c a x
lam x t b = Lam t (abstract1 x b)

for :: Eq x => x -> Expr c a x -> Expr c a x -> Expr c a x
for x i o = For i (abstract1 x o)

-- instantiate a constructor in an expression
eInstantiateC1 :: Eq a => Monad c => c a -> Expr (Scope () c) a x -> Expr c a x
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
eInstantiateC1 t (Concat l) = Concat (map (eInstantiateC1 t) l)
eInstantiateC1 a (For i o) = For (eInstantiateC1 a i) (hoistScope (eInstantiateC1 a) o)
eInstantiateC1 a (If c t e) = If (eInstantiateC1 a c) (eInstantiateC1 a t) (eInstantiateC1 a e)
eInstantiateC1 a (Record l) = Record (mapSnd (eInstantiateC1 a) l)
eInstantiateC1 a (Rmap x t y) = Rmap (eInstantiateC1 a x) (instantiate1 a t) (eInstantiateC1 a y)
eInstantiateC1 a (Rfold l m n d) = Rfold (eInstantiateC1 a l) (eInstantiateC1 a m) (eInstantiateC1 a n) (instantiate1 a d)
eInstantiateC1 a (Proj l e) = Proj l (eInstantiateC1 a e)
eInstantiateC1 a (Table n t) = Table n (instantiate1 a t)
eInstantiateC1 a (Eq t l r) = Eq (instantiate1 a t) (eInstantiateC1 a l) (eInstantiateC1 a r)
eInstantiateC1 a (And l r) = And (eInstantiateC1 a l) (eInstantiateC1 a r)
eInstantiateC1 a (Typecase c b i s l r t) = Typecase (instantiate1 a c) (eInstantiateC1 a b) (eInstantiateC1 a i) (eInstantiateC1 a s) (eInstantiateC1 (lift a) l) (eInstantiateC1 (lift a) r) (eInstantiateC1 (lift a) t)
eInstantiateC1 a (Tracecase x l i f r oe oa) = Tracecase
  (eInstantiateC1 a x)
  (hoistScope (eInstantiateC1 a) l)
  (hoistScope (eInstantiateC1 a) i)
  (hoistScope (eInstantiateC1 (lift a)) f)
  (hoistScope (eInstantiateC1 a) r)
  (hoistScope (eInstantiateC1 (lift a)) oe)
  (hoistScope (eInstantiateC1 a) oa)
eInstantiateC1 a (Trace tr e) = Trace (fmap (instantiate1 a) tr) (eInstantiateC1 a e)

-- abstract over a constructor in an expression
eAbstractC1 :: Eq a => Functor c => a -> Expr c a x -> Expr (Scope () c) a x
eAbstractC1 _ (Const c) = Const c
eAbstractC1 _ (Var x) = Var x
eAbstractC1 a (Lam t b) = Lam (abstract1 a t) (hoistScope (eAbstractC1 a) b)
eAbstractC1 a (Fix t b) = Fix (abstract1 a t) (hoistScope (eAbstractC1 a) b)
eAbstractC1 a ((:$) l r) = (:$) (eAbstractC1 a l) (eAbstractC1 a r)
eAbstractC1 a (TLam k b) = TLam k (eAbstractC1 a b)
eAbstractC1 a ((:§) e c) = (:§) (eAbstractC1 a e) (abstract1 a c)
eAbstractC1 a (Empty c) = Empty (abstract1 a c)
eAbstractC1 a (Singleton e) = Singleton (eAbstractC1 a e)
eAbstractC1 t (Concat l) = Concat (map (eAbstractC1 t) l)
eAbstractC1 a (For i o) = For (eAbstractC1 a i) (hoistScope (eAbstractC1 a) o)
eAbstractC1 a (If c t e) = If (eAbstractC1 a c) (eAbstractC1 a t) (eAbstractC1 a e)
eAbstractC1 a (Record l) = Record (mapSnd (eAbstractC1 a) l)
eAbstractC1 a (Rmap f t r) = Rmap (eAbstractC1 a f) (abstract1 a t) (eAbstractC1 a r)
eAbstractC1 a (Proj l r) = Proj l (eAbstractC1 a r)
eAbstractC1 a (Table n t) = Table n (abstract1 a t) -- not needed I think, should be base types..
eAbstractC1 a (Eq t l r) = Eq (abstract1 a t) (eAbstractC1 a l) (eAbstractC1 a r)
eAbstractC1 a (And l r) = And (eAbstractC1 a l) (eAbstractC1 a r)
eAbstractC1 a (Typecase c b i s l r t) = Typecase (abstract1 a c) (eAbstractC1 a b) (eAbstractC1 a i) (eAbstractC1 a s) (eAbstractC1 a l) (eAbstractC1 a r) (eAbstractC1 a t)
eAbstractC1 a (Trace tr e) = Trace (fmap (abstract1 a) tr) (eAbstractC1 a e)


tlam :: Eq a => Monad c => a -> Kind -> Expr c a x -> Expr c a x
tlam a k b = TLam k (eAbstractC1 a b) -- this should be actual abstract, not my misnamed one, I think


isApp :: Expr c a x -> Bool
isApp ((:$) _ _) = True
isApp ((:§) _ _) = True
isApp _ = False

prettyExpr :: ([String], [String]) -> Bool -> Expr Type String String -> Doc
prettyExpr ([], _) _ _ = error "ran out of variable names"
prettyExpr (_, []) _ _ = error "ran out of type variable names"
prettyExpr _ _ (Const Bottom) = red (char '⊥')
prettyExpr _ _ (Const (Bool b)) = text (show b)
prettyExpr _ _ (Const (Int b)) = text (show b)
prettyExpr _ _ (Const (String b)) = dquotes $ text b
prettyExpr _ _ (Var x) = text x
prettyExpr (vs, tvs) p (e ::: t) =
  -- pparens p $ prettyExpr (vs, tvs) True e <+> char ':' <+> T.prettyType tvs True t
  prettyExpr (vs, tvs) p e
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
prettyExpr ns p (Concat l) = pparens p $ align (cat (punctuate (text " ++ ") (map (\e -> prettyExpr ns True e) l)))
prettyExpr ns p (Eq _t l r) = pparens p $ prettyExpr ns True l <+> text "==" <+> prettyExpr ns True r
prettyExpr ns p (And l r) = pparens p $ prettyExpr ns True l <+> text "&&" <+> prettyExpr ns True r
prettyExpr (v:vs, tvs) p (For i o) = pparens p $ hang 2 $
  bold (text "for") <+> (hang 3 (parens (text v <+> text "<-" <+> prettyExpr (v:vs, tvs) False i))) P.<$> prettyExpr (vs, tvs) False (instantiate1 (Var v) o)
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
prettyExpr ns@(_, tvs) p (Rmap f _t r) = pparens p $
  bold (text "rmap") <+> prettyExpr ns True f <+> prettyExpr ns True r <+> T.prettyType tvs True _t
prettyExpr ns@(_, tvs) p (Rfold f a r _t) = pparens p $
  bold (text "rfold") <+> prettyExpr ns True f <+> prettyExpr ns True a <+> prettyExpr ns True r <+> T.prettyType tvs True _t
prettyExpr (v:vs, tv:tvs) p (Tracecase x l i f r oe a) = pparens p $
  bold (text "tracecase") <+> prettyExpr (v:vs, tv:tvs) False x <+> bold (text "of") <$$>
  (indent 2 $
    text "Lit" <+> text v <+> text "=>" <+> prettyExpr (vs, tv:tvs) False (instantiate1 (Var v) l) <$$>
    text "If" <+> text v <+> text "=>" <+> prettyExpr (vs, tv:tvs) False (instantiate1 (Var v) i) <$$>
    text "For" <+> text tv <+> text v <+> text "=>" <+> prettyExpr (vs, tvs) False (eInstantiateC1 (T.Var tv) (instantiate1 (Var v) f)) <$$>
    text "Row" <+> text v <+> text "=>" <+> prettyExpr (vs, tv:tvs) False (instantiate1 (Var v) r) <$$>
    text "Op==" <+> text tv <+> text v <+> text "=>" <+> prettyExpr (vs, tvs) False (eInstantiateC1 (T.Var tv) (instantiate1 (Var v) oe)) <$$>
    text "Op&&" <+> text v <+> text "=>" <+> prettyExpr (vs, tv:tvs) False (instantiate1 (Var v) r))
prettyExpr ns p (Trace TrLit e) = pparens p $ green (text "Lit") <+> prettyExpr ns True e
prettyExpr ns p (Trace TrRow e) = pparens p $ green (text "Row") <+> prettyExpr ns True e
prettyExpr ns p (Trace TrIf e) = pparens p $ green (text "If") <+> prettyExpr ns True e
prettyExpr ns@(_, tvs) p (Trace (TrFor c) e) = pparens p $ green (text "For") <+> {- T.prettyType tvs True c <+> -} prettyExpr ns True e
prettyExpr ns@(_, tvs) p (Trace (TrEq c) e) = pparens p $ green (text "Eq") <+> {- prettyType tvs True c <+> -} prettyExpr ns True e
prettyExpr ns p (Trace TrAnd e) = pparens p $ green (text "And") <+> prettyExpr ns True e

instance Show (Expr Type String String) where
  showsPrec _ e = displayS (renderPretty 0.6 90 (prettyExpr (evars, tvars) False e))
