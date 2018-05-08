{-# LANGUAGE InstanceSigs, FlexibleContexts, DeriveFunctor, StandaloneDeriving, TemplateHaskell, RankNTypes, ScopedTypeVariables, TupleSections, LambdaCase #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Type where

import Data.Deriving (deriveShow1, deriveEq1)
import Data.List (sort, nub, foldl', all)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import qualified Text.PrettyPrint.ANSI.Leijen as P
import Bound ((>>>=), Var(B,F))
import Bound.Scope
import Common
import Control.Monad (ap)
import GHC.Exts (sortWith)

import           Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

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
  | Index -- TODO
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
prettyType _ _ c | c == valuetf = text "VALUE"
prettyType _ _ c | c == lineagetf = text "LINEAGE"
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
prettyType avs _ (List a) = brackets (prettyType avs False a)
--pparens p $ text "List" <+> prettyType avs True a
prettyType avs p (Trace a) = pparens p $ text "Trace" <+> prettyType avs True a
-- prettyType _ p (Record (Var x)) = pparens p $ text "Record" <+> text x
prettyType avs p (Record row) = braces (prettyRow avs row)
prettyType avs p (Typerec x b i s l r t) = pparens p $ bold (text "Typerec") <+> prettyType avs True x </>
  tupled (map (prettyType avs False) [b, i, s, l, r, t])
prettyType avs p (Arrow a b) = pparens p $ prettyType avs True a <+> text "->" <+> prettyType avs True b
prettyType (av:avs) p (Forall k t) = pparens p $ bold (char '∀') <> text av <> char '.' <> prettyType avs False (instantiate1 (Var av) t)
prettyType _ p Index = pparens p $ text "Index"

prettyRow :: [String] -> Type String -> Doc
prettyRow _ RowNil = empty
prettyRow _ (Var x) = char '|' <> text x
prettyRow avs (RowCons l c RowNil) =
  dullblue (text l) <> char ':' <+> prettyType avs False c
prettyRow avs (RowCons l c r) =
  dullblue (text l) <> char ':' <+> prettyType avs False c <> char ',' <+> prettyRow avs r
prettyRow _ _ = error "not a row"

-- the TRACE type function
tracetf :: Type a
tracetf = Lam KType $ toScope $ Typerec (Var (B ()))
  (Trace Bool) (Trace Int) (Trace String)
  (Lam KType (toScope (Lam KType (toScope (List (Var (B ())))))))
  (Lam KRow (toScope (Lam KRow (toScope (Record (Var (B ())))))))
  (Lam KType (toScope (Lam KType (toScope (Trace (Var (F (B ()))))))))

-- the VALUE type function
valuetf :: Type a
valuetf = Lam KType $ toScope $ Typerec (Var (B ()))
  Bool Int String
  (Lam KType (toScope (Lam KType (toScope (List (Var (B ())))))))
  (Lam KRow (toScope (Lam KRow (toScope (Record (Var (B ())))))))
  (Lam KType (toScope (Lam KType (toScope (Var (B ()))))))

-- the WHERE type function
wheretf :: Type a
wheretf = Lam KType $ toScope $ Typerec (Var (B ()))
  (w Bool)
  (w Int)
  (w String)
  (Lam KType (toScope (Lam KType (toScope (List (Var (F (B ()))))))))
  (Lam KRow (toScope (Lam KRow (toScope (Record (Var (F (B ()))))))))
  (Lam KType (toScope (Lam KType (toScope (Var (F (B ()))))))) -- not  sure about this one
  where w t = record [("data", t), ("table", String), ("column", String), ("row", Int)]

-- the LINEAGE type function
lineagetf :: Type a
lineagetf = Lam KType $ toScope $ Typerec (Var (B ()))
  Bool Int String
  (Lam KType (toScope (Lam KType (toScope (List (l (Var (B ()))))))))
  (Lam KRow (toScope (Lam KRow (toScope (Record (Var (B ())))))))
  (Lam KType (toScope (Lam KType (toScope (Var (B ()))))))
  where l a = record [("data", a),
                      ("lineage", List (record [("table", String), ("row", Int)]))]

record :: [(Label, Type a)] -> Type a
record = Record . listToRow

listToRow :: [(Label, Type a)] -> Type a
listToRow [] = RowNil
listToRow ((l,t):r) = RowCons l t (listToRow r)

rowToList :: Type a -> [(Label, Type a)]
rowToList = sortWith fst . rowToList'
  where
    rowToList' RowNil = []
    rowToList' (RowCons l c r) = (l, c) : rowToList' r
    rowToList' _ = error "not a row"

norm :: Eq a => Type a -> Type a
norm Bool = Bool
norm Int = Int
norm String = String
norm (Var v) = Var v
norm (Lam k b) = Lam k b -- can't normalize under binder, because .. why?
norm (Forall k b) = Forall k b -- same
norm (App f a) = case norm f of
  (Lam _ b) -> norm $ instantiate1 a b
  e -> error $ "trying to apply non-type function "
norm (List c) = List (norm c)
norm (Trace c) = Trace (norm c)
norm (Record c) = Record (norm c)
norm (Arrow a b) = Arrow (norm a) (norm b)
norm RowNil = RowNil
norm (RowCons l c r) = RowCons l (norm c) (norm r)
norm (Typerec x b i s l r t) = norm $ case norm x of
  Bool -> b; Int -> i; String -> s
  List c -> App (App l c) (Typerec c b i s l r t)
  Record c -> App (App r c) (RowMap (Lam KType (toScope (Typerec (Var (B ())) (F <$> b) (F <$> i) (F <$> s) (F <$> l) (F <$> r) (F <$> t)))) c)
  Trace c -> App (App t c) (Typerec c b i s l r t)
  -- stuck -> error $ show stuck-- Typerec stuck b i s l r t
norm (RowMap _ RowNil) = RowNil
norm (RowMap f (RowCons l c r)) = norm $ RowCons l (App f c) (RowMap f r)
norm (RowMap _ e) = error $ "Can't RowMap over " -- ++ show e

isBaseType Bool = True
isBaseType Int = True
isBaseType String = True
isBaseType _ = False

genLabel = Gen.string (Range.constant 1 3) Gen.lower

genDistinctLabels = nub <$> Gen.list (Range.constant 1 3) genLabel

genBaseType :: Gen (Type a)
genBaseType = Gen.choice (pure <$> [ Bool, Int, String ])

genClosedRow :: Gen (Type a)
genClosedRow = genDistinctLabels >>= genRowFromLabels

genRowFromLabels :: [Label] -> Gen (Type a)
genRowFromLabels labels = do
  pairs <- traverse (\l -> genType >>= pure . (l,)) (sort labels)
  pure (foldr (\(l, t) r -> RowCons l t r) RowNil pairs)
  
genType :: Gen (Type a)
genType = Gen.recursive Gen.choice
  [ genBaseType ]
  [ Gen.subtermM genType (pure . List)
  , do
      row <- genClosedRow
      pure (Record row)
  ]
