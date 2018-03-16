{-# LANGUAGE InstanceSigs, FlexibleContexts, DeriveFunctor, StandaloneDeriving, TemplateHaskell, RankNTypes, ScopedTypeVariables, TupleSections, LambdaCase #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Type where

import Data.Deriving (deriveShow1, deriveEq1)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import qualified Text.PrettyPrint.ANSI.Leijen as P
import Bound ((>>>=), Var(B,F))
import Bound.Scope.Simple
import Common
import Control.Monad (ap)
import GHC.Exts (sortWith)

data Kind = KType | KRow | KArrow Kind Kind
  deriving (Show, Eq)

prettyKind :: Kind -> Doc
prettyKind KType = text "Type"
prettyKind KRow = text "Row"
prettyKind (KArrow l r) = parens $ prettyKind l <+> text "->" <+> prettyKind r

data Type a
  = Bool
  | Int
  | String
  | Var a
  | Lam Kind (Scope () Type a)
  | Arrow (Type a) (Type a)
  | Forall Kind (Scope () Type a)
  | App (Type a) (Type a)
  | List (Type a)
  | Trace (Type a)
  -- I don't really want another datatype for constructor rows
  | Record (Type a)
  | RowNil
  | RowCons Label (Type a) (Type a)
  | Typerec (Type a) (Type a) (Type a) (Type a) (Type a) (Type a) (Type a)
  | RowMap (Type a) (Type a)
  deriving (Functor)

deriveEq1 ''Type
deriving instance Eq a => Eq (Type a)
deriveShow1 ''Type
deriving instance Show a => Show (Type a)

instance Applicative Type where
  pure = return
  (<*>) = ap

instance Monad Type where
  return = Var

  Bool >>= _ = Bool
  Int >>= _ = Int
  String >>= _ = String
  Var a >>= f = f a
  Lam k b >>= f = Lam k (b >>>= f)
  Forall k b >>= f = Forall k (b >>>= f)
  App a b >>= f = App (a >>= f) (b >>= f)
  Arrow a b >>= f = Arrow (a >>= f) (b >>= f)
  List a >>= f = List (a >>= f)
  Trace a >>= f = Trace (a >>= f)
  Record r >>= f = Record (r >>= f)
  RowNil >>= _ = RowNil
  RowCons l c r >>= f = RowCons l (c >>= f) (r >>= f)
  RowMap c d >>= f = RowMap (c >>= f) (d >>= f)
  Typerec x b i s l r t >>= f = Typerec (x >>= f) (b >>= f) (i >>= f) (s >>= f) (l >>= f) (r >>= f) (t >>= f)

clam :: Eq a => a -> Kind -> Type a -> Type a
clam a k b = Lam k (abstract1 a b)

prettyType :: [String] -> Bool -> Type String -> Doc
prettyType [] _ _ = error "ran out of type variables during constructor pretty printing"
-- TODO these might be needed for rowmap and stuff
prettyType _ _ c | c == tracetf = text "TRACE"
prettyType _ _ c | c == valuetf = text "TRACE"
prettyType _ _ RowNil = error "row outside of record"
prettyType _ _ (RowCons _ _ _) = error "row outside of record"
prettyType _ _ Bool = text "Bool"
prettyType _ _ Int = text "Int"
prettyType _ _ String = text "String"
prettyType _ _ (Var a) = text a
prettyType (av:avs) p (Lam k body) = pparens p $ hang 2 $ group $
  bold (char 'λ') <> text av <> kindAnnotation <> char '.' <> {- P.<$$> -} prettyType avs False (instantiate1 (Var av) body)
  where kindAnnotation = case k of
          KType -> empty
          _ -> char ':' <> prettyKind k
prettyType avs p (App a b) = pparens p $
  prettyType avs True a <+> prettyType avs True b
prettyType avs p (List a) = pparens p $ text "List" <+> prettyType avs True a
prettyType avs p (Trace a) = pparens p $ text "Trace" <+> prettyType avs True a
prettyType _ p (Record (Var x)) = pparens p $ text "Record" <+> text x
prettyType avs p (Record row) = pparens p $ text "Record" <+> parens (prettyRow avs row)
prettyType avs p (Typerec x b i s l r t) = pparens p $ bold (text "Typerec") <+> prettyType avs True x </>
  tupled (map (prettyType avs False) [b, i, s, l, r, t])
prettyType avs p (Arrow a b) = pparens p $ prettyType avs True a <+> text "->" <+> prettyType avs True b
prettyType (av:avs) p (Forall k t) = pparens p $ char '∀' <> text av <> char '.' <> prettyType avs False (instantiate1 (Var av) t)

prettyRow :: [String] -> Type String -> Doc
prettyRow _ RowNil = char '⋅'
prettyRow avs (RowCons l c RowNil) =
  text l <> char ':' <+> prettyType avs False c
prettyRow avs (RowCons l c r) =
  text l <> char ':' <+> prettyType avs False c <> char ',' <+> prettyRow avs r
prettyRow _ (Var x) = text x
prettyRow _ _ = error "not a row"

-- the TRACE type function
tracetf :: Type a
tracetf = Lam KType $ toScope $ Typerec (Var (B ()))
  (Trace Bool) (Trace Int) (Trace String)
  (Lam KType (toScope (Lam KType (toScope (List (Var (B ())))))))
  (Lam KRow (toScope (Lam KRow (toScope (Record (Var (B ())))))))
  (Lam KType (toScope (Lam KType (toScope (Trace (Var (B ())))))))

-- the VALUE type function
valuetf :: Type a
valuetf = Lam KType $ toScope $ Typerec (Var (B ()))
  Bool Int String
  (Lam KType (toScope (Lam KType (toScope (List (Var (B ())))))))
  (Lam KRow (toScope (Lam KRow (toScope (Record (Var (B ())))))))
  (Lam KType (toScope (Lam KType (toScope (Var (B ()))))))

rowToList :: Type a -> [(Label, Type a)]
rowToList = sortWith fst . rowToList'
  where
    rowToList' RowNil = []
    rowToList' (RowCons l c r) = (l, c) : rowToList' r
    rowToList' _ = error "not a row"

norm :: Show a => Eq a => Type a -> Type a
norm Bool = Bool
norm Int = Int
norm String = String
norm (Var v) = Var v
norm (Lam k b) = Lam k b -- can't normalize under binder, because .. why?
norm (App f a) = case norm f of
  (Lam _ b) -> norm $ instantiate1 a b
  e -> error $ "trying to apply non-type function " ++ show e
norm (List c) = List (norm c)
norm (Trace c) = Trace (norm c)
norm (Record c) = Record (norm c)
norm RowNil = RowNil
norm (RowCons l c r) = RowCons l (norm c) (norm r)
norm (Typerec x b i s l r t) = norm $ case norm x of
  Bool -> b; Int -> i; String -> s
  List c -> App (App l c) (Typerec c b i s l r t)
  Record c -> App (App r c) (RowMap (Lam KType (toScope (Typerec (Var (B ())) (F <$> b) (F <$> i) (F <$> s) (F <$> l) (F <$> r) (F <$> t)))) c)
  Trace c -> App (App t c) (Typerec c b i s l r t)
  stuck -> error $ show stuck-- Typerec stuck b i s l r t
norm (RowMap _ RowNil) = RowNil
norm (RowMap f (RowCons l c r)) = norm $ RowCons l (App f c) (RowMap f r)
norm (RowMap _ e) = error $ "Can't RowMap over " ++ show e
