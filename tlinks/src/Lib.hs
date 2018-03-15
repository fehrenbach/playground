{-# LANGUAGE InstanceSigs, FlexibleContexts, DeriveFunctor, StandaloneDeriving, TemplateHaskell, RankNTypes, ScopedTypeVariables, TupleSections, LambdaCase #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Lib
    ( someFunc
    ) where

import Bound ((>>>=), Var(B,F))
import Bound.Scope.Simple
import Common
import Control.Exception (assert)
import Control.Monad (ap)
import Control.Monad.Morph (lift, hoist)
import Data.Functor.Classes (Eq1)
import Data.Deriving (deriveShow1, deriveEq1)
import Text.PrettyPrint.ANSI.Leijen hiding (string, nest, (<$>))
import qualified Text.PrettyPrint.ANSI.Leijen as P

import Type (Type, Kind)
import qualified Type as T

-- I'm sure there's a better way to do this, but my hoogle-fu is insufficient
mapSnd :: (a -> b) -> [(l, a)] -> [(l, b)]
mapSnd _ [] = []
mapSnd f ((a,b):r) = (a, f b) : mapSnd f r

tvars, evars :: [String]
tvars = ["α", "β", "γ"] <> [ "α" <> show x | x <- [0 :: Integer ..] ]
evars = ["x", "y", "z"] <> [ "x" <> show x | x <- [0 :: Integer ..] ]

data Trace c
  = TrLit
  | TrIfThen
  | TrIfElse
  | TrFor c
  | TrRow
  | TrEq c
  deriving (Functor)

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
  | Proj Label (c a) (Expr c a x)
  | Table String (c a) -- type of ELEMENTS/ROWS that is, a record type, not a list type
  | Eq (c a) (Expr c a x) (Expr c a x) -- equality specialized to a type
  | Typecase (c a) (Expr c a x) (Expr c a x) (Expr c a x) (Expr (Scope () c) a x) (Expr (Scope () c) a x) (Expr (Scope () c) a x)
  | Trace (Trace (c a)) (Expr c a x)
  | Tracecase (Expr c a x) -- discriminant
               (Scope () (Expr c a) x) -- Lit
               (Scope () (Expr c a) x) -- IfThen
               (Scope () (Expr c a) x) -- IfElse
               (Scope () (Expr (Scope () c) a) x) -- For
               (Scope () (Expr c a) x) -- Row
               (Scope () (Expr (Scope () c) a) x) -- Eq
  deriving (Functor)

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
  Proj l t e >>= f = Proj l t (e >>= f)
  Table n t >>= _ = Table n t
  Eq t l r >>= f = Eq t (l >>= f) (r >>= f)
  Typecase c b i s l r t >>= f = Typecase c (b >>= f) (i >>= f) (s >>= f) (l >>= liftCE . f) (r >>= liftCE . f) (t >>= liftCE . f)
  Tracecase x l t e g r q >>= f =
    Tracecase (x >>= f) (l >>>= f) (t >>>= f) (e >>>= f) (g >>>= liftCE . f) (r >>>= f) (q >>>= liftCE . f)
  Trace tc e >>= f = Trace tc (e >>= f)

liftCE :: Monad c => Expr c a b -> Expr (Scope () c) a b
liftCE Bottom = Bottom
liftCE (Const c) = (Const c)
liftCE (Var x) = Var x
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
liftCE (Proj l t e) = Proj l (lift t) (liftCE e)
liftCE (Table n t) = Table n (lift t)
liftCE (Eq t l r) = Eq (lift t) (liftCE l) (liftCE r)
liftCE (Typecase c b i s l r t) = Typecase (lift c) (liftCE b) (liftCE i) (liftCE s) (liftCE l) (liftCE r) (liftCE t)
liftCE (Tracecase x l it ie f r oe) = Tracecase
  (liftCE x)
  (hoistScope liftCE l)
  (hoistScope liftCE it)
  (hoistScope liftCE ie)
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
eInstantiateC1 a (Proj l t e) = Proj l (instantiate1 a t) (eInstantiateC1 a e)
eInstantiateC1 a (Table n t) = Table n (instantiate1 a t)
eInstantiateC1 a (Eq t l r) = Eq (instantiate1 a t) (eInstantiateC1 a l) (eInstantiateC1 a r)
eInstantiateC1 a (Typecase c b i s l r t) = Typecase (instantiate1 a c) (eInstantiateC1 a b) (eInstantiateC1 a i) (eInstantiateC1 a s) (eInstantiateC1 (lift a) l) (eInstantiateC1 (lift a) r) (eInstantiateC1 (lift a) t)
eInstantiateC1 a (Tracecase x l it ie f r oe) = Tracecase
  (eInstantiateC1 a x)
  (hoistScope (eInstantiateC1 a) l)
  (hoistScope (eInstantiateC1 a) it)
  (hoistScope (eInstantiateC1 a) ie)
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
eAbstractC1 a (Proj l t r) = Proj l (abstract1 a t) (eAbstractC1 a r)
eAbstractC1 a (Table n t) = Table n (abstract1 a t) -- not needed I think, should be base types..
eAbstractC1 a (Eq t l r) = Eq (abstract1 a t) (eAbstractC1 a l) (eAbstractC1 a r)
eAbstractC1 a (Typecase c b i s l r t) = Typecase (abstract1 a c) (eAbstractC1 a b) (eAbstractC1 a i) (eAbstractC1 a s) (eAbstractC1 a l) (eAbstractC1 a r) (eAbstractC1 a t)

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
                   -- IfThen
                   (toScope ((:$) ((:§) (Var (F (F (B ())))) (toScope (toScope (T.Trace (T.Var (B ()))))))
                              (Proj "then" (toScope (toScope (T.Record (T.RowCons "then" (T.Trace (T.Var (B ()))) (T.RowCons "cond" (T.Trace T.Bool) T.RowNil))))) (Var (B ())))))
                   -- IfElse
                   (toScope ((:$) ((:§) (Var (F (F (B ())))) (toScope (toScope (T.Trace (T.Var (B ()))))))
                              (Proj "else" (toScope (toScope (T.Record (T.RowCons "else" (T.Trace (T.Var (B ()))) (T.RowCons "cond" (T.Trace T.Bool) T.RowNil))))) (Var (B ())))))
                   -- For
                   (toScope ((:$) ((:§) (Var (F (F (B ())))) (toScope (toScope (toScope (T.Trace (T.Var (F (B ()))))))))
                             (Proj "out" (toScope (toScope (toScope (T.Record T.RowNil {- TODO -}))))
                              (Var (B ())))))
                   -- Row
                   (toScope (Proj "data" (toScope (toScope (T.Record (T.RowCons "data" (T.Var (B ())) {- TODO other fields -} T.RowNil))))
                             (Var (B ()))))
                   -- OpEq
                   (toScope (Eq (toScope (toScope (toScope (T.Var (B ())))))
                             ((:$) ((:§) (Var (F (F (B ())))) (toScope (toScope (toScope (T.Trace (T.Var (B ())))))))
                               (Proj "left" eqRType (Var (B ()))))
                             ((:$) ((:§) (Var (F (F (B ())))) (toScope (toScope (toScope (T.Trace (T.Var (B ())))))))
                               (Proj "right" eqRType (Var (B ()))))))
                   )))
        where
          eqRType = toScope (toScope (toScope (T.Record (T.RowCons "left" (T.Trace (T.Var (B ()))) (T.RowCons "right" (T.Trace (T.Var (B ()))) T.RowNil)))))

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
prettyExpr _ _ (Const (String b)) = text (show b)
prettyExpr _ _ (Var x) = text x
prettyExpr (v:vs, tvs) p (Fix t e) = pparens p $ hang 2 $ group $
  bold (text "fix") <+> parens (text v <> colon <> T.prettyType tvs False t) <> dot P.<$$> prettyExpr (vs, tvs) False (instantiate1 (Var v) e)
prettyExpr (v:vs, tvs) p (Lam t b) = pparens p $ hang 2 $ group $
  bold (char 'λ') <> text v <> typeAnnotation <> char '.' P.<$$> prettyExpr (vs, tvs) False (instantiate1 (Var v) b)
  where typeAnnotation = char ':' <> T.prettyType tvs False t
prettyExpr (vs, tv:tvs) p (TLam k b) = pparens p $ hang 2 $ group $
  bold (char 'Λ') <> text tv <> kindAnnotation <> char '.' P.<$$> prettyExpr (vs, tvs) False (eInstantiateC1 (T.Var tv) b)
  where kindAnnotation = case k of
          T.KType -> empty
          _ -> char ':' <> T.prettyKind k
-- prettyExpr ns p (EVariant l e) = pparens p $
  -- dullgreen (text l) <+> prettyExpr ns True e
prettyExpr ns p ((:$) l r) = pparens p $ hang 2 $
  prettyExpr ns (not $ isApp l) l P.<$> prettyExpr ns True r
prettyExpr (vs, tvs) p ((:§) e c) = pparens p $
  prettyExpr (vs, tvs) (not $ isApp e) e </> T.prettyType tvs True c
prettyExpr _ _ (Empty _) = brackets empty 
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
prettyExpr ns p (Proj l _t e) = pparens p $
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
prettyExpr (v:vs, tv:tvs) p (Tracecase x l it ie f r oe) = pparens p $
  bold (text "tracecase") <+> prettyExpr (v:vs, tv:tvs) False x <+> bold (text "of") <$$>
  (indent 2 $
    text "Lit" <+> text v <+> text "=>" <+> prettyExpr (vs, tv:tvs) False (instantiate1 (Var v) l) <$$>
    text "IfThen" <+> text v <+> text "=>" <+> prettyExpr (vs, tv:tvs) False (instantiate1 (Var v) it) <$$>
    text "IfElse" <+> text v <+> text "=>" <+> prettyExpr (vs, tv:tvs) False (instantiate1 (Var v) ie) <$$>
    text "For" <+> text tv <+> text v <+> text "=>" <+> prettyExpr (vs, tvs) False (eInstantiateC1 (T.Var tv) (instantiate1 (Var v) f)) <$$>
    text "Row" <+> text v <+> text "=>" <+> prettyExpr (vs, tv:tvs) False (instantiate1 (Var v) r) <$$>
    text "Op==" <+> text tv <+> text v <+> text "=>" <+> prettyExpr (vs, tvs) False (eInstantiateC1 (T.Var tv) (instantiate1 (Var v) oe)))
prettyExpr ns p (Trace TrLit e) = pparens p $ green (text "Lit") <+> prettyExpr ns True e
prettyExpr ns p (Trace TrRow e) = pparens p $ green (text "Row") <+> prettyExpr ns True e
prettyExpr ns p (Trace TrIfThen e) = pparens p $ green (text "IfThen") <+> prettyExpr ns True e
prettyExpr ns p (Trace TrIfElse e) = pparens p $ green (text "IfElse") <+> prettyExpr ns True e
prettyExpr ns@(_, tvs) p (Trace (TrFor c) e) = pparens p $ green (text "For") <+> {- prettyType tvs True c <+> -} prettyExpr ns True e
prettyExpr ns@(_, tvs) p (Trace (TrEq c) e) = pparens p $ green (text "Eq") <+> {- prettyType tvs True c <+> -} prettyExpr ns True e

{-
betaReduce :: Eq a => Monad c => Expr c a x -> Expr c a x
betaReduce Bottom = Bottom
betaReduce ETrue = ETrue
betaReduce EFalse = EFalse
betaReduce (EString s) = EString s
-- TODO might want to check types before reducing
betaReduce (EApp (ELam _t b) x) = instantiate1 x b
betaReduce (EApp f x) = EApp (betaReduce f) (betaReduce x)
-- TODO might want to check kinds before reducing
betaReduce (E(:§) (ETLam _k b) c) = eInstantiateC1 c b
betaReduce (E(:§) e c) = E(:§) (betaReduce e) c
betaReduce (EVar x) = EVar x
betaReduce (ELam t b) = ELam t (hoistScope betaReduce b)
betaReduce (ETLam k b) = ETLam k (betaReduce b)
-- betaReduce (EVariant l e) = EVariant l (betaReduce e)
betaReduce (ESingletonList e) = ESingletonList (betaReduce e)
betaReduce EEmptyList = EEmptyList
betaReduce (EConcat l r) = EConcat (betaReduce l) (betaReduce r)
betaReduce (EFor t i o) = EFor t (betaReduce i) (hoistScope betaReduce o)
betaReduce (EIf c t e) = EIf (betaReduce c) (betaReduce t) (betaReduce e)
betaReduce (ERecord l) = ERecord (mapSnd betaReduce l)
betaReduce (EProj l t e) = EProj l t (betaReduce e)
betaReduce t@(ETable _ _) = t
betaReduce (EEq t l r) = EEq t (betaReduce l) (betaReduce r)
betaReduce (ETypecase c b i s l r t) = ETypecase c (betaReduce b) (betaReduce i) (betaReduce s) (betaReduce l) (betaReduce r) (betaReduce t)
betaReduce (EFix t e) = EFix t (hoistScope betaReduce e)
betaReduce (ERmap m t n) = ERmap (betaReduce m) t (betaReduce n)
betaReduce (ETracecase x l it ie f r oe) = ETracecase
  (betaReduce x)
  (hoistScope betaReduce l)
  (hoistScope betaReduce it)
  (hoistScope betaReduce ie)
  (hoistScope betaReduce f)
  (hoistScope betaReduce r)
  (hoistScope betaReduce oe)

betaReduceN :: Eq a => Monad c => Int -> Expr c a x -> Expr c a x
betaReduceN 0 e = e
betaReduceN n e = betaReduceN (n-1) (betaReduce e)
-}


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
unroll n (Proj l t e) = Proj l t (unroll n e)
unroll _ (Table name t) = Table name t
unroll n (Rmap a t b) = Rmap (unroll n a) t (unroll n b)
unroll n (Eq t l r) = Eq t (unroll n l) (unroll n r)
unroll n (Typecase c b i s l r t) = Typecase c (unroll n b) (unroll n i) (unroll n s) (unroll n l) (unroll n r) (unroll n t)
unroll n (Tracecase x l it ie f r oe) = Tracecase
  (unroll n x)
  (hoistScope (unroll n) l)
  (hoistScope (unroll n) it)
  (hoistScope (unroll n) ie)
  (hoistScope (unroll n) f)
  (hoistScope (unroll n) r)
  (hoistScope (unroll n) oe)
unroll n (Trace tr e) = Trace tr (unroll n e)


one :: Show a => Eq a => Expr Type a x -> Expr Type a x
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
one (For _ (Empty _) _) = Empty (error "Type of the body?...")
one (For _ (Singleton e) o) = instantiate1 e o
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
  (map (\(l,t) -> (l, (:$) ((:§) f t) (Proj l (T.Record row) r)))
    (T.rowToList row))
one (Rmap _ _ _) = error "TODO need to normalize type (and switch to constructor, not type to begin with, I think"
one (Proj l _ (Record fs)) = case lookup l fs of
  Nothing -> error "label not found in record"
  Just e -> e
one (Proj l t e) = Proj l t (one e)
-- one (EEq _ l r) | l == r = ETrue --
one (Eq t l r) = Eq t (one l) (one r)
one (Typecase c b i s l r t) = case c of
  T.Bool -> b; T.Int -> i; T.String -> s;
  T.List c' -> eInstantiateC1 c' l
  T.Record c' -> eInstantiateC1 c' r
  T.Trace c' -> eInstantiateC1 c' t
  _ -> Typecase (T.norm c) b i s l r t
one (Tracecase x l it ie f r oe) = case x of
  Trace tr t -> instantiate1 t (case tr of
                                   TrLit -> l; TrIfThen -> it; TrIfElse -> ie; TrRow -> r
                                   TrFor c -> hoistScope (eInstantiateC1 c) f
                                   TrEq c -> hoistScope (eInstantiateC1 c) oe)
  x' -> Tracecase (one x') l it ie f r oe
one (Trace tr e) = Trace tr (one e)

{-
wtf :: Expr c a x -> String
wtf EVar{} = "EVar"
wtf Bottom{} = "Bottom"
wtf ETrue = "ETrue"
wtf EFalse = "EFalse"
wtf (EString s) = "EString " ++ s
wtf EIf{} = "EIf"
wtf ELam{} = "ELam"
wtf EFix{} = "EFix"
wtf (E(:$) a b) = "E(:$) (" ++ wtf a ++ ") (" ++ wtf b ++ ")"
            -- (ETLam _ _)
            -- (E(:§) _ _)
            -- (EVariant _ _)
            -- EEmptyList
-}
tid :: Scope () (Expr c a) x
tid = toScope (Var (B ()))

trace :: Show x => Eq a => Scope () (Expr Type a) x -> Expr Type a x -> Expr Type a x
trace k (Var v) = instantiate1 (Var v) k
trace k (Const c) = instantiate1 (Trace TrLit (Const c)) k
trace k (If c t e) = If (value :§ T.Trace T.Bool :$ trace tid c)
  (trace (k `nest` itScope) t)
  (trace (k `nest` ieScope) e)
  where
    itScope = toScope (Trace TrIfThen (Record [("cond", F <$> trace k c), ("then", Var (B ()))]))
    ieScope = toScope (Trace TrIfElse (Record [("cond", F <$> trace k c), ("else", Var (B ()))]))
trace k (Empty t) = Empty t
trace k (Singleton e) = Singleton (trace k e)
trace k (Concat l r) = Concat (trace k l) (trace k r)
trace k (For t i o) = For (T.App T.tracetf t) (trace tid i)
  (toScope (trace ((F <$> k) `nest` fScope) (fromScope o)))
  where
    fScope = toScope (Trace (TrFor undefined) (Record [("in", Var (F (B ()))), ("out", Var (B ()))]))
trace k (Record fs) = case typeof (Record fs) of
  T.Record row -> Record ((\(l,_t) -> case lookup l fs of
                                        Nothing -> error "field not present"
                                        Just f -> (l, trace k f)) <$> T.rowToList row)
  _ -> error "not a record type"
trace k (Proj l _ r) = Proj l undefined (trace k r)
trace _ Bottom = error "Can't trace Bottom"

typeof :: Expr Type a x -> Type a
typeof (Const (Bool _)) = T.Bool
typeof (Const (Int _)) = T.Int
typeof (Const (String _)) = T.String
typeof (Record fs) = T.Record (rowType fs)
  where rowType [] = T.RowNil
        rowType ((l,e):es) = T.RowCons l (typeof e) (rowType es)

-- Takes two expressions which each have one hole in them, and plugs
-- the hole in the first expression with the second expression,
-- yielding an expression with one hole in it, or the other way round.
nest :: Eq a => Scope () (Expr Type a) x -> Scope () (Expr Type a) x -> Scope () (Expr Type a) x
nest a b = toScope $ splat (Var . F) (const (fromScope b)) a

-- trace k (For t i o) = For (T.App T.tracetf t) (trace tid i) (hoistScope (trace (

trace' e = trace tid e

putE :: Expr Type String String -> IO ()
putE e = do
  putDoc $ prettyExpr (evars, tvars) False e
  putStrLn ""

putC :: Type String -> IO ()
putC c = do
  putDoc $ T.prettyType tvars False c
  putStrLn ""

showTraced e = do
  putStrLn "===================="
  putE e
  putStrLn "-------trace---->"
  putE $ {- (!! 20) . iterate one $ unroll 2 $ -} trace' e

true, false :: Expr c a x
true = Const (Bool True)
false = Const (Bool False)

int :: Int -> Expr c a x
int = Const . Int
string :: String -> Expr c a x
string = Const . String

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
  showTraced $ for "a" T.Bool (Singleton true) (for "b" T.Bool (Singleton false) (Singleton (Record [("a", Var "a"), ("b", Var "b")])))

  let recRec = Record [("a", Record [("b", true)])]
  showTraced $ Proj "b" undefined (Proj "a" undefined recRec)

  showTraced $ for "x" (T.Record (T.RowCons "b" T.Bool T.RowNil)) (Singleton (Record [("b", true)])) (Singleton (Var "x"))
  showTraced $ for "x" (T.Record (T.RowCons "b" T.Bool T.RowNil)) (Singleton (Record [("b", true)])) (Singleton (Proj "b" undefined (Var "x")))

  putStrLn "Okay, so the more compact traces have the same problem. That's good to know. I think I can fix it by applying a distribution function to subtraces"

  -- putStrLn "TRACE:"
  -- putDoc $ prettyType tvars False tracetf
  -- putStrLn ""
  -- putStrLn "VALUE:"
  -- putDoc $ prettyType tvars False valuetf
  -- putStrLn ""

  -- let notTrue = EIf ETrue EFalse ETrue
  -- putE notTrue

  -- let constantFor = efor "x" (TT CBool) (ESingletonList ETrue) (ESingletonList ETrue)
  -- putE constantFor
  -- let simpleFor = efor "m" (TT (CVar "am")) (EVar "M") (EVar "N") --(ESingeltonList (EVar "m"))
  -- putE simpleFor

  -- putE $ betaReduceN 0 $ E(:$) (trace (TT (CList (CVar "an"))) simpleFor) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 1 $ E(:$) (trace (TT (CList (CVar "an"))) simpleFor) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 2 $ E(:$) (trace (TT (CList (CVar "an"))) simpleFor) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 3 $ E(:$) (trace (TT (CList (CVar "an"))) simpleFor) (traceId (CVar "TRACE"))
  -- putE $ (!! 8) . iterate one $ E(:$) (trace (TT (CList (CVar "an"))) simpleFor) traceId

  -- let forNestedBase = efor "a" (TT CBool) (ESingletonList ETrue) (efor "b" (TT CBool) (ESingletonList EFalse) (ESingletonList (EVar "y")))
  -- putE forNestedBase

  -- let forNested = efor "a" (TT CBool) (ESingletonList ETrue) (efor "b" (TT CBool) (ESingletonList EFalse) (ESingletonList (ERecord [("a", EVar "a"), ("b", EVar "b")])))
  -- putE forNested
  -- putE $ (!! 20) . iterate one $ E(:$) (trace (TT (CList (CRecord (CRowCons "a" CBool (CRowCons "b" CBool CRowNil))))) forNested) traceId

{-
  let forIf = efor "x" (TT CBool) (EConcat (EVar "xs") (EVar "ys")) (EIf (EVar "x") (ESingletonList (EVar "x")) EEmptyList)
  putE forIf
  -- putE $ betaReduceN 0 $ E(:$) (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 1 $ E(:$) (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 2 $ E(:$) (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 3 $ E(:$) (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 4 $ E(:$) (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 5 $ E(:$) (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 6 $ E(:$) (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 7 $ E(:$) (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 8 $ E(:$) (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  putE $ betaReduceN 9 $ E(:$) (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))

  let record1 = ERecord [("b", ETrue), ("a", EFalse)]
  putE $ record1
  -- putE $ betaReduceN 0  $ E(:$) (trace (TT (CRecord (CRowCons "b" CBool (CRowCons "a" CBool CRowNil)))) record1) (traceId (CVar "TRACE"))
  putE $ betaReduceN 4 $ E(:$) (trace (TT (CRecord (CRowCons "b" CBool (CRowCons "a" CBool CRowNil)))) record1) traceId

  let recRec = ERecord [("a", ERecord [("b", ETrue)])]
  putE recRec
  putE $ betaReduceN 5 $ E(:$) (trace (TT (CRecord (CRowCons "a" (CRecord (CRowCons "b" CBool CRowNil)) CRowNil))) recRec) traceId

  let proj1 = EProj "b" (TT (CRecord (CRowCons "b" CBool (CRowCons "a" CBool CRowNil)))) record1
  putE $ proj1
  putE $ betaReduceN 7 $ E(:$) (trace (TT CBool) proj1) traceId

  let projRecRec = EProj "b" (TT (CRecord (CRowCons "b" CBool CRowNil))) (EProj "a" (TT (CRecord (CRowCons "a" (CRecord (CRowCons "b" CBool CRowNil)) CRowNil))) recRec)
  putE projRecRec
  putE $ betaReduceN 11 $ E(:$) (trace (TT CBool) projRecRec) traceId
  -}
  -- putE $ value

  -- let crab = T.Record (T.RowCons "a" T.String (T.RowCons "b" T.Bool T.RowNil))

  -- let tableABs = Table "abs" crab
  -- let tTableABs = E(:$) (trace (TT (CList crab)) tableABs) traceId
  -- putE tableABs
  -- putE $ tTableABs
  -- putStrLn "traced:"
  -- putE $ (!! 3) . iterate one $ tTableABs

  -- putStrLn "----------------------------------------------------------------------"

  -- let asFromTable = efor "x" (TT crab) tableABs (ESingletonList (EProj "a" (TT crab) (EVar "x")))
  -- let unTAsFromTable = EApp (E(:§) value (CList (CTrace CString)))
  --                         (EApp (trace (TT (CList CString)) asFromTable) traceId)
  -- putE asFromTable
  -- putStrLn "~>"
  -- putE $ ((!! 22) . iterate one) $ unroll 2 $ unTAsFromTable

  -- let forIfProj = efor "x" (TT crab) tableABs (ESingletonList (EIf (EProj "b" (TT crab) (EVar "x")) (EProj "a" (TT crab) (EVar "x")) (EString "fake")))
  -- putE $ forIfProj
  -- putE $ trace (TT (CList CString)) forIfProj
  -- putE $ (!! 22) . iterate one $ unroll 1 $ EApp (trace (TT (CList CString)) forIfProj) traceId

  -- putStrLn "----------------------------------------------------------------------"

  -- let xFromTable = efor "x" (TT crab) tableABs (ESingletonList (EVar "x"))
  -- putE $ xFromTable
  -- putStrLn "traced:"
  -- let tXFromTable = EApp (trace (TT (CList crab)) xFromTable) traceId
  -- putE $ tXFromTable
  -- putE $ ((!! 12) . iterate one) $ unroll 0 $ tXFromTable

  -- putStrLn "Ugh. No, that's still broken. Tables? Comprehensions? Records?"

  -- let forfor = elam "foo" TBool $ efor "x" TBool (efor "y" TBool (EVar "L") (EApp (EVar "M") (EVar "y"))) (EApp (EApp (EVar "N") (EVar "x")) (EVar "foo"))
  -- putE forfor
  -- putE $ one $ forfor

  -- putStrLn "-----------------------------------------------------"

  -- let valueTXFromTable = E(:§) value (CApp tracetf (CList crab))
  -- putStrLn "specialized value function"
  -- let specVal = ((!! 11) . iterate one) $ unroll 4 $ valueTXFromTable
  -- putE $ specVal

  -- let unTXFromTable = EApp specVal tXFromTable
  -- putStrLn "whole thing normalized:"
  -- putE $ (!! 24) . iterate one $ unroll 4 $ unTXFromTable
  -- putE $ ((!! 100) . iterate one) $ unroll 3 $ valueTXFromTable
  -- let unTTXFromTable = EApp valueTXFromTable tXFromTable
  -- putE $ ((!! 200) . iterate one) $ unroll 4 $ unTTXFromTable
  --                        
  -- putE $ tXFromTable
  -- putE $ ((!! 16) . iterate one) $ unroll 2 $ tXFromTable


  -- let selfJoin = efor "x" (TT crab) tableABs (efor "y" (TT crab) tableABs
  --                  (EIf (EEq (TT CString) (EProj "a" (TT crab) (EVar "x")) (EProj "a" (TT crab) (EVar "y")))
  --                       (ESingletonList (ERecord [("x", EVar "x"), ("y", EVar "y")]))
  --                       EEmptyList))

  putE $ Empty T.Bool
  putE $ Singleton (Const (Bool True))
  putE $ Concat (Empty T.Bool) (Singleton (Const (Bool True)))
  putE $ one $ Concat (Empty T.Bool) (Singleton (Const (Bool True)))


  putStrLn "end"

  -- putE selfJoin
  -- putE $ betaReduceN 17 $ EApp (trace (TT (CList (CRecord (CRowCons "x" crab (CRowCons "y" crab CRowNil))))) selfJoin) traceId
  -- putE $ ((!! 18) . iterate one) $ unroll 1 $ EApp (trace (TT (CList (CRecord (CRowCons "x" crab (CRowCons "y" crab CRowNil))))) selfJoin) (E(:§) value (CApp tracetf (CList (CRecord (CRowCons "x" crab (CRowCons "y" crab CRowNil))))))



  -- putE $ EApp (trace (TT (CList crab)) tableABs) traceId
  -- putE $ ((!! 3) . iterate one) $ EApp (trace (TT (CList crab)) tableABs) traceId
  -- putC (CList (CRecord (CRowCons "a" (CTrace CString) (CRowCons "b" (CTrace CBool) CRowNil))))
  -- putC (CApp tracetf (CList crab))
  -- putC (normC (CApp tracetf (CList crab)))

  


  -- let eqLists = EEq (TT (CList CString)) (ESingletonList (EString "a")) EEmptyList
  -- putE eqLists
  -- putE $ betaReduceN 6 $ EApp (trace (TT CBool) eqLists) traceId

  -- let eqEq = EEq (TT CBool) eqLists ETrue
  -- putE eqEq
  -- putE $ betaReduceN 2 $ EApp (trace (TT CBool) eqEq) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 4 $ EApp (trace (TT CBool) eqEq) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 6 $ EApp (trace (TT CBool) eqEq) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 8 $ EApp (trace (TT CBool) eqEq) traceId

  -- putE $ value

  -- putE selfJoin
  -- putE $ betaReduceN 17 $ EApp (trace (TT (CList (CRecord (CRowCons "x" crab (CRowCons "y" crab CRowNil))))) selfJoin) traceId
  -- let selfJoinValue = EApp (EApp (trace (TT (CList (CRecord (CRowCons "x" crab (CRowCons "y" crab CRowNil))))) selfJoin) traceId) value
  -- putE $ spec $ betaReduceN 20 $ unroll 4 $ betaReduceN 20 selfJoinValue

  -- let foo = EFix (TT CBool) (toScope $ EApp (EApp (EVar (F "bla")) (EVar (B ()))) (EVar (F "blubb")))
  -- let bar = EFix (TT CBool) (toScope $ EApp (EApp (EApp (EApp (EVar (F "a")) (EVar (B ()))) (EVar (F "b"))) (F <$> foo)) (EVar (F "c")))
  -- putE foo
  -- putE $ unroll 0 foo
  -- putE $ unroll 1 foo
  -- putE $ unroll 2 foo
  -- putE bar
  -- putE $ unroll 0 bar
  -- putE $ unroll 1 bar
  -- putE $ unroll 2 bar


  -- let valBool = EApp (E(:§) value (CTrace CBool)) (ETrace (TrLit ETrue)) --(EVariant "Lit" ETrue)
  -- putE valBool
  -- putE (unroll 0 valBool)
  -- putE (unroll 1 valBool)
  -- putE (unroll 2 valBool)
  -- putE $ betaReduceN 1 $ spec $ spec $ unroll 1 valBool
  -- putE $ betaReduceN 2 $ spec $ spec $ unroll 1 valBool
  -- putE $ ((!! 4) . iterate one) $ unroll 1 valBool

  -- let simpleRmap = ERmap traceId (TT (CRecord (CRowCons "a" (CTrace CBool) (CRowCons "b" (CTrace CString) CRowNil)))) (ERecord [("a", EVariant "Lit" ETrue), ("b", EVariant "Lit" (EString "foo"))])
  -- putE simpleRmap
  -- putE $ ((!! 0) . iterate one) $ simpleRmap
  -- putE $ ((!! 1) . iterate one) $ simpleRmap
  -- putE $ ((!! 2) . iterate one) $ simpleRmap
  -- putE $ ((!! 3) . iterate one) $ simpleRmap
  -- putE $ ((!! 4) . iterate one) $ simpleRmap

  -- let omega = EFix (TT CBool) (toScope (EApp (EVar (B ())) (EVar (B ()))))
  -- putE $ omega
  -- putE $ unroll 1 $ omega

{-  let projForNested = efor "x" (TT (CRecord (CRowCons "b" CBool (CRowCons "a" CBool CRowNil)))) forNested (ESingletonList (EProj "a" (TT (CRecord (CRowCons "a" CBool (CRowCons "b" CBool CRowNil)))) (EVar "x")))
  putE projForNested
  putE $ betaReduceN 12 $ EApp (trace (TT (CList CBool)) projForNested) (traceId (CVar "TRACE"))
  -- Fuck. Something is still wrong. Record projection, I think. Maybe I need RMAP?

  let proj2 = efor "x" (TT (CRecord (CRowCons "a" CBool CRowNil))) (ESingletonList (ERecord [("a", ETrue)])) (ESingletonList (EProj "a" (TT (CRecord (CRowCons "a" CBool CRowNil))) (EVar "x")))
  putE proj2
  -- putE $ betaReduceN 0 $ EApp (trace (TT (CList CBool)) proj2) (traceId (CVar "TRACE"))
  putE $ betaReduceN 10 $ EApp (trace (TT (CList CBool)) proj2) (traceId (CVar "TRACE"))

-}
