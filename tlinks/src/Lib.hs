{-# LANGUAGE InstanceSigs, FlexibleContexts, DeriveFunctor, StandaloneDeriving, TemplateHaskell, RankNTypes, ScopedTypeVariables, TupleSections, LambdaCase #-}

module Lib
    ( someFunc
    , clam
    , tforall
    , elam
    , etlam
    , efor
    ) where

import Bound ((>>>=), Var(B,F))
import Bound.Scope.Simple
import Control.Exception (assert)
import GHC.Exts (sortWith)
import Control.Monad (ap)
import Control.Monad.Morph (lift)
import Data.Functor.Classes (Eq1)
import Data.Deriving (deriveEq1)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import qualified Text.PrettyPrint.ANSI.Leijen as P

-- I'm sure there's a better way to do this, but my hoogle-fu is insufficient
mapSnd :: (a -> b) -> [(l, a)] -> [(l, b)]
mapSnd _ [] = []
mapSnd f ((a,b):r) = (a, f b) : mapSnd f r

pparens :: Bool -> Doc -> Doc
pparens True d = black (char '(') <> d <> black (char ')')
pparens False d = d

tvars, evars :: [String]
tvars = ["α", "β", "γ"] <> [ "α" <> show x | x <- [0 :: Integer ..] ]
evars = ["x", "y", "z"] <> [ "x" <> show x | x <- [0 :: Integer ..] ]

data Kind = KType | KArrow Kind Kind
  deriving (Eq)

prettyKind :: Kind -> Doc
prettyKind KType = text "Type"
prettyKind (KArrow l r) = parens $ prettyKind l <+> text "->" <+> prettyKind r

type Label = String

data Constructor a
  = CBool
  | CString
  | CVar a {- Uhm. I'd quite like a type annotation on variables, but then how do I write `return`?! -}
  | CLambda Kind (Scope () Constructor a)
  | CApp (Constructor a) (Constructor a)
  | CList (Constructor a)
  | CTrace (Constructor a)
  -- I don't really want another datatype for constructor rows
  | CRecord (Constructor a)
  | CRowNil
  | CRowCons Label (Constructor a) (Constructor a)
  deriving (Functor)

deriveEq1 ''Constructor
deriving instance Eq a => Eq (Constructor a)

instance Applicative Constructor where
  pure = return
  (<*>) = ap

instance Monad Constructor where
  return = CVar

  CBool >>= _ = CBool
  CString >>= _ = CString
  CVar a >>= f = f a
  CLambda k b >>= f = CLambda k (b >>>= f)
  CApp a b >>= f = CApp (a >>= f) (b >>= f)
  CList a >>= f = CList (a >>= f)
  CTrace a >>= f = CTrace (a >>= f)
  CRecord r >>= f = CRecord (r >>= f)
  CRowNil >>= _ = CRowNil
  CRowCons l c r >>= f = CRowCons l (c >>= f) (r >>= f)

clam :: Eq a => a -> Kind -> Constructor a -> Constructor a
clam a k b = CLambda k (abstract1 a b)

prettyConstructor :: [String] -> Bool -> Constructor String -> Doc
prettyConstructor [] _ _ = error "ran out of type variables during constructor pretty printing"
-- TODO these might be needed for rowmap and stuff
prettyConstructor _ _ CRowNil = error "row outside of record"
prettyConstructor _ _ (CRowCons _ _ _) = error "row outside of record"
prettyConstructor _ _ CBool = text "Bool*"
prettyConstructor _ _ CString = text "String*"
prettyConstructor _ _ (CVar a) = text a
prettyConstructor (av:avs) p (CLambda k body) = pparens p $
  char 'λ' <> text av <> char ':' <> prettyKind k <> char '.' <> prettyConstructor avs False (instantiate1 (CVar av) body)
prettyConstructor avs p (CApp a b) = pparens p $
  prettyConstructor avs True a <+> prettyConstructor avs True b
prettyConstructor avs p (CList a) = pparens p $ text "List*" <+> prettyConstructor avs True a
prettyConstructor avs p (CTrace a) = pparens p $ text "Trace*" <+> prettyConstructor avs True a
prettyConstructor avs p (CRecord row) = pparens p $ text "Record*" <+> parens (prettyCRow avs row)

prettyCRow :: [String] -> Constructor String -> Doc
prettyCRow _ CRowNil = char '⋅'
prettyCRow avs (CRowCons l c CRowNil) =
  text l <> char ':' <+> prettyConstructor avs False c
prettyCRow avs (CRowCons l c r) =
  text l <> char ':' <+> prettyConstructor avs False c <> char ',' <+> prettyCRow avs r
prettyCRow _ _ = error "not a crow"

data Type c a
  = TBool
  | TT (c a)
  -- the body is a type with an additional bound constructor variable
  | TForall Kind (Type (Scope () c) a)
  | TArrow (Type c a) (Type c a)
  | TList (Type c a)
  | TTrace (Type c a)
  deriving (Functor)

deriveEq1 ''Type
deriving instance (Eq1 c, Eq (c a), Eq a) => Eq (Type c a)

tforall :: Eq a => a -> Kind -> Type Constructor a -> Type Constructor a
tforall a k body = TForall k (tAbstract1 a body)

tAbstract1 :: Functor constructor => Eq a => a -> Type constructor a -> Type (Scope () constructor) a
tAbstract1 = go abstract1
  where
    go :: forall c c' a. Eq a
       => (forall v. Eq v => v -> c v -> c' v)
      -> a -> Type c a -> Type c' a
    go _ _ TBool = TBool
    go f a (TT c) = TT (f a c)
    go f a (TForall k b) = TForall k (go f' a b)
      where
        f' v = Scope . f (F v) . unscope
    go f a (TArrow l r) = TArrow (go f a l) (go f a r)
    go f a (TList t) = TList (go f a t)
    go f a (TTrace t) = TTrace (go f a t)

prettyType :: [String] -> Bool -> Type Constructor String -> Doc
prettyType [] _ _ = error "ran out of type variables during type pretty printing"
prettyType _ _ TBool = text "Bool"
prettyType avs _ (TT c) = char 'T' <> parens (prettyConstructor avs False c)
prettyType (av:avs) p (TForall k body) = pparens p $
  bold (char '∀') <> text av <> kindAnnotation <> char '.' <> prettyType avs p (tInstantiate1 (CVar av) body)
  where kindAnnotation = case k of
          KType -> empty
          _ -> char ':' <> prettyKind k
prettyType avs p (TArrow a b) = pparens p $ prettyType avs True a <+> text "->" <+> prettyType avs True b
prettyType avs p (TList a) = pparens p $ text "List" <+> prettyType avs True a
prettyType avs p (TTrace a) = pparens p $ text "Trace" <+> prettyType avs True a

tInstantiate1 :: forall operand b a.
  (Applicative operand, Monad operand) =>
  operand a -> Type (Scope b operand) a -> Type operand a
tInstantiate1 = go instantiate1
  where
    go :: forall o o' u. (forall v. operand v -> o v -> o' v) -> operand u -> Type o u -> Type o' u
    go _ _ TBool = TBool
    go f a (TT c) = TT (f a c)
    go f a (TForall k b) = TForall k (go f' a b)
      where
        f' v = Scope . f (fmap F v) . unscope
    go f a (TArrow l r) = TArrow (go f a l) (go f a r)
    go f a (TList t) = TList (go f a t)
    go f a (TTrace t) = TTrace (go f a t)

data Expr c a x
  = ETrue | EFalse
  | EString String
  | EVar x
  | EIf (Expr c a x) (Expr c a x) (Expr c a x)
  | ELam (Type c a) (Scope () (Expr c a) x)
  | EApp (Expr c a x) (Expr c a x)
  | ETLam Kind (Expr (Scope () c) a x)
  | ETApp (Expr c a x) (c a)
  | EVariant Label (Expr c a x) -- add type hint?
  | EEmptyList -- add type hint? (Type c a)
  | ESingletonList (Expr c a x)
  | EConcat (Expr c a x) (Expr c a x)
  -- The Type is the type of ELEMENTS of the first Expr argument
  | EFor (Type c a) (Expr c a x) (Scope () (Expr c a) x)
  | ERecord [(Label, Expr c a x)]
  -- the Type is the type of the record. I need this for tracing.
  | EProj Label (Type c a) (Expr c a x)
  | ETable String (Type c a) -- type of ELEMENTS/ROWS that is, a record type, not a list type
  | EEq (Type c a) (Expr c a x) (Expr c a x) -- equality specialized to a type
  deriving (Functor)

instance (Eq a, Monad c) => Applicative (Expr c a) where
  pure = return
  (<*>) = ap

instance (Eq a, Monad c) => Monad (Expr c a) where
  return = EVar

  ETrue >>= _ = ETrue
  EFalse >>= _ = EFalse
  EString s >>= _ = EString s
  EVar x >>= f = f x
  ELam t b >>= f = ELam t (b >>>= f)
  EFor t e b >>= f = EFor t (e >>= f) (b >>>= f)
  EApp l r >>= f = EApp (l >>= f) (r >>= f)
  ETLam k b >>= f = ETLam k (b >>= liftCE . f)
  ETApp e c >>= f = ETApp (e >>= f) c
  EVariant l e >>= f = EVariant l (e >>= f)
  EEmptyList >>= _ = EEmptyList
  ESingletonList e >>= f = ESingletonList (e >>= f)
  EConcat l r >>= f = EConcat (l >>= f) (r >>= f)
  ERecord le >>= f = ERecord (map (\(l, x) -> (l, x >>= f)) le)
  EIf i t e >>= f = EIf (i >>= f) (t >>= f) (e >>= f)
  EProj l t e >>= f = EProj l t (e >>= f)
  ETable n t >>= _ = ETable n t
  EEq t l r >>= f = EEq t (l >>= f) (r >>= f)

liftCE :: Monad c => Expr c a b -> Expr (Scope () c) a b
liftCE ETrue = ETrue
liftCE EFalse = EFalse
liftCE (EString s) = EString s
liftCE (EVar x) = EVar x
liftCE (ELam t b) = ELam (liftCT t) (hoistScope liftCE b)
liftCE (EFor t e b) = EFor (liftCT t) (liftCE e) (hoistScope liftCE b)
liftCE (EApp l r) = EApp (liftCE l) (liftCE r)
liftCE (ETLam k b) = ETLam k (liftCE b)
liftCE (ETApp e c) = ETApp (liftCE e) (lift c)
liftCE (EVariant l e) = EVariant l (liftCE e)
liftCE EEmptyList = EEmptyList
liftCE (ESingletonList e) = ESingletonList (liftCE e)
liftCE (EConcat l r) = EConcat (liftCE l) (liftCE r)
liftCE (EIf i t e) = EIf (liftCE i) (liftCE t) (liftCE e)
liftCE (ERecord l) = ERecord (mapSnd liftCE l)
liftCE (EProj l t e) = EProj l (liftCT t) (liftCE e)
liftCE (ETable n t) = ETable n (liftCT t)
liftCE (EEq t l r) = EEq (liftCT t) (liftCE l) (liftCE r)

liftCT :: Monad c => Type c a -> Type (Scope () c) a
liftCT TBool = TBool
liftCT (TT c) = TT (lift c)
liftCT (TForall k c) = TForall k (liftCT c)
liftCT (TArrow a b) = TArrow (liftCT a) (liftCT b)
liftCT (TList a) = TList (liftCT a)
liftCT (TTrace a) = TTrace (liftCT a)

elam :: Eq x => x -> Type c a -> Expr c a x -> Expr c a x
elam x t b = ELam t (abstract1 x b)

efor :: Eq x => x -> Type c a -> Expr c a x -> Expr c a x -> Expr c a x
efor x t i o = EFor t i (abstract1 x o)

-- instantiate a constructor in an expression
eInstantiateC1 :: Eq a => Monad c => c a -> Expr (Scope () c) a x -> Expr c a x
eInstantiateC1 _ ETrue = ETrue
eInstantiateC1 _ EFalse = EFalse
eInstantiateC1 _ (EString s) = EString s
eInstantiateC1 _ (EVar x) = EVar x
eInstantiateC1 a (ELam t b) = ELam (tInstantiate1 a t) (hoistScope (eInstantiateC1 a) b)
eInstantiateC1 a (EApp l r) = EApp (eInstantiateC1 a l) (eInstantiateC1 a r)
eInstantiateC1 a (ETLam k b) = ETLam k (eInstantiateC1 (lift a) b)
eInstantiateC1 a (ETApp e c) = ETApp (eInstantiateC1 a e) (instantiate1 a c)
eInstantiateC1 _ EEmptyList = EEmptyList
eInstantiateC1 a (EVariant l e) = EVariant l (eInstantiateC1 a e)
eInstantiateC1 a (ESingletonList e) = ESingletonList (eInstantiateC1 a e)
eInstantiateC1 a (EConcat l r) = EConcat (eInstantiateC1 a l) (eInstantiateC1 a r)
eInstantiateC1 a (EFor t i o) = EFor (tInstantiate1 a t) (eInstantiateC1 a i) (hoistScope (eInstantiateC1 a) o)
eInstantiateC1 a (EIf c t e) = EIf (eInstantiateC1 a c) (eInstantiateC1 a t) (eInstantiateC1 a e)
eInstantiateC1 a (ERecord l) = ERecord (mapSnd (eInstantiateC1 a) l)
eInstantiateC1 a (EProj l t e) = EProj l (tInstantiate1 a t) (eInstantiateC1 a e)
eInstantiateC1 a (ETable n t) = ETable n (tInstantiate1 a t)
eInstantiateC1 a (EEq t l r) = EEq (tInstantiate1 a t) (eInstantiateC1 a l) (eInstantiateC1 a r)

-- abstract over a constructor in an expression
eAbstractC1 :: Eq a => Functor c => a -> Expr c a x -> Expr (Scope () c) a x
eAbstractC1 _ ETrue = ETrue
eAbstractC1 _ EFalse = EFalse
eAbstractC1 _ (EString s) = EString s
eAbstractC1 _ (EVar x) = EVar x
eAbstractC1 a (ELam t b) = ELam (tAbstract1 a t) (hoistScope (eAbstractC1 a) b)
eAbstractC1 a (EApp l r) = EApp (eAbstractC1 a l) (eAbstractC1 a r)
eAbstractC1 a (ETLam k b) = ETLam k (eAbstractC1 a b)
eAbstractC1 a (ETApp e c) = ETApp (eAbstractC1 a e) (abstract1 a c)
eAbstractC1 _ EEmptyList = EEmptyList
eAbstractC1 a (EVariant l e) = EVariant l (eAbstractC1 a e)
eAbstractC1 a (ESingletonList e) = ESingletonList (eAbstractC1 a e)
eAbstractC1 a (EConcat l r) = EConcat (eAbstractC1 a l) (eAbstractC1 a r)
eAbstractC1 a (EFor t i o) = EFor (tAbstract1 a t) (eAbstractC1 a i) (hoistScope (eAbstractC1 a) o)
eAbstractC1 a (EIf c t e) = EIf (eAbstractC1 a c) (eAbstractC1 a t) (eAbstractC1 a e)
eAbstractC1 a (ERecord l) = ERecord (mapSnd (eAbstractC1 a) l)
eAbstractC1 a (EProj l t r) = EProj l (tAbstract1 a t) (eAbstractC1 a r)
eAbstractC1 a (ETable n t) = ETable n (tAbstract1 a t) -- not needed I think, should be base types..
eAbstractC1 a (EEq t l r) = EEq (tAbstract1 a t) (eAbstractC1 a l) (eAbstractC1 a r)

etlam :: Eq a => Monad c => a -> Kind -> Expr c a x -> Expr c a x
etlam a k b = ETLam k (eAbstractC1 a b) -- this should be actual abstract, not my misnamed one, I think

-- polyId' :: Expr Constructor String String
-- polyId' = etlam "a" KType (elam "ex" (TT (CVar "a")) (EVar "ex"))

-- polyId :: Expr Constructor a x
-- polyId = ETLam KType $ ELam (TT $ toScope (CVar (B ()))) $ toScope (EVar (B ()))

traceId :: Constructor a -> Expr Constructor a x
traceId tracetf = ETLam KType $ ELam (TT $ toScope (CApp (F <$> tracetf) (CVar (B ())))) $ toScope (EVar (B ()))

isApp :: Expr c a x -> Bool
isApp (EApp _ _) = True
isApp (ETApp _ _) = True
isApp _ = False

prettyExpr :: ([String], [String]) -> Bool -> Expr Constructor String String -> Doc
prettyExpr ([], _) _ _ = error "ran out of variable names"
prettyExpr (_, []) _ _ = error "ran out of type variable names"
prettyExpr _ _ ETrue = text "true"
prettyExpr _ _ EFalse = text "false"
prettyExpr _ _ (EVar x) = text x
prettyExpr _ _ (EString s) = text (show s)
prettyExpr (v:vs, tvs) p (ELam t b) = pparens p $ hang 2 $ group $
  bold (char 'λ') <> text v <> char ':' <> prettyType tvs False t <> char '.' P.<$$> prettyExpr (vs, tvs) False (instantiate1 (EVar v) b)
prettyExpr (vs, tv:tvs) p (ETLam k b) = pparens p $ hang 2 $ group $
  bold (char 'Λ') <> text tv <> kindAnnotation <> char '.' P.<$$> prettyExpr (vs, tvs) False (eInstantiateC1 (CVar tv) b)
  where kindAnnotation = case k of
          KType -> empty
          _ -> char ':' <> prettyKind k
prettyExpr ns p (EVariant l e) = pparens p $
  dullgreen (text l) <+> prettyExpr ns True e
prettyExpr ns p (EApp l r) = pparens p $ hang 2 $
  prettyExpr ns (not $ isApp l) l P.<$> prettyExpr ns True r
prettyExpr (vs, tvs) p (ETApp e c) = pparens p $
  prettyExpr (vs, tvs) (not $ isApp e) e </> prettyConstructor tvs True c
prettyExpr _ _ EEmptyList = text "[]"
prettyExpr ns _ (ESingletonList e) = brackets $ prettyExpr ns False e
prettyExpr ns p (EConcat l r) = pparens p $ prettyExpr ns True l <+> text "++" <+> prettyExpr ns True r
prettyExpr ns p (EEq _t l r) = pparens p $ prettyExpr ns True l <+> text "==" <+> prettyExpr ns True r
prettyExpr (v:vs, tvs) p (EFor t i o) = pparens p $ hang 2 $
  bold (text "for") <+> (hang 3 (parens (text v <> typeAnnotation <+> text "<-" P.<$> prettyExpr (v:vs, tvs) False i))) P.<$> prettyExpr (vs, tvs) False (instantiate1 (EVar v) o)
  where typeAnnotation = char ':' <+> prettyType tvs False t
prettyExpr _ _ (ERecord []) = braces empty
prettyExpr ns _ (ERecord l) = group $ braces $ align (cat (punctuate (comma <> space) (map (\(lbl, e) -> blue (text lbl) <+> char '=' <+> prettyExpr ns False e) l)))
prettyExpr ns p (EIf c t e) = pparens p $ group $
  bold (text "if") <+> prettyExpr ns False c P.<$>
  bold (text "then") <+> prettyExpr ns False t P.<$>
  bold (text "else") <+> prettyExpr ns False e
prettyExpr ns p (EProj l _t e) = pparens p $
  prettyExpr ns True e <> char '.' <> blue (text l)
prettyExpr (_, tvs) p (ETable n t) = pparens p $
  bold (text "table") <+> text (show n) <+> prettyType tvs True t

betaReduce :: Eq a => Monad c => Expr c a x -> Expr c a x
betaReduce ETrue = ETrue
betaReduce EFalse = EFalse
betaReduce (EString s) = EString s
-- TODO might want to check types before reducing
betaReduce (EApp (ELam _t b) x) = instantiate1 x b
betaReduce (EApp f x) = EApp (betaReduce f) (betaReduce x)
-- TODO might want to check kinds before reducing
betaReduce (ETApp (ETLam _k b) c) = eInstantiateC1 c b
betaReduce (ETApp e c) = ETApp (betaReduce e) c
betaReduce (EVar x) = EVar x
betaReduce (ELam t b) = ELam t (hoistScope betaReduce b)
betaReduce (ETLam k b) = ETLam k (betaReduce b)
betaReduce (EVariant l e) = EVariant l (betaReduce e)
betaReduce (ESingletonList e) = ESingletonList (betaReduce e)
betaReduce EEmptyList = EEmptyList
betaReduce (EConcat l r) = EConcat (betaReduce l) (betaReduce r)
betaReduce (EFor t i o) = EFor t (betaReduce i) (hoistScope betaReduce o)
betaReduce (EIf c t e) = EIf (betaReduce c) (betaReduce t) (betaReduce e)
betaReduce (ERecord l) = ERecord (mapSnd betaReduce l)
betaReduce (EProj l t e) = EProj l t (betaReduce e)
betaReduce t@(ETable _ _) = t
betaReduce (EEq t l r) = EEq t (betaReduce l) (betaReduce r)

betaReduceN :: Eq a => Monad c => Int -> Expr c a x -> Expr c a x
betaReduceN 0 e = e
betaReduceN n e = betaReduceN (n-1) (betaReduce e)


rowToList :: Constructor a -> [(Label, Constructor a)]
rowToList = sortWith fst . rowToList'
  where
    rowToList' CRowNil = []
    rowToList' (CRowCons l c r) = (l, c) : rowToList' r
    rowToList' _ = error "not a row"

ttype :: Constructor a -> Type Constructor a
ttype tracetf = TForall KType $
  TArrow (TT $ toScope $ CApp (fmap F tracetf) (CVar (B ())))
         (TT $ toScope $ CApp (fmap F tracetf) (CVar (B ())))

trace' :: Eq a => Constructor a -> x -> Type Constructor a -> Expr Constructor a x -> Expr Constructor a x
trace' _ _ _ (ELam _ _) = error "cannot trace lambda"
trace' _ _ _ (ETLam _ _) = error "cannot trace Lambda"
trace' _ _ _ (EApp _ _) = error "cannot trace app"
trace' _ _ _ (EVariant _ _) = error "cannot trace variant constructor"
trace' tracetf value (TT constructor) expression = tr constructor expression
  where
    tr CBool ETrue = ELam (ttype tracetf) $ toScope $
      EApp (ETApp (EVar (B ())) CBool) (EVariant "Lit" ETrue)
    tr CBool EFalse = ELam (ttype tracetf) $ toScope $
      EApp (ETApp (EVar (B ())) CBool) (EVariant "Lit" EFalse)
    tr CString (EString s) = ELam (ttype tracetf) $ toScope $
      EApp (ETApp (EVar (B ())) CString) (EVariant "Lit" (EString s))
    tr c (EVar x) = ELam (ttype tracetf) $ toScope (EApp (ETApp (EVar (B ())) c) (EVar (F x)))
    tr _ EEmptyList = ELam (ttype tracetf) $ toScope $ EEmptyList
    tr (CList c) (ESingletonList e) = ELam (ttype tracetf) $ toScope $
      ESingletonList (EApp (fmap F (tr c e)) (EVar (B ())))
    tr (CList c) (EConcat l r) = ELam (ttype tracetf) $ toScope $
      EConcat (EApp (F <$> tr (CList c) l) (EVar (B ())))
              (EApp (F <$> tr (CList c) r) (EVar (B ())))
    tr (CRecord row) (ERecord flds) = ELam (ttype tracetf) $ toScope $
      ERecord $ zipWith (\(l, t) (l', x) -> assert (l == l') $
                          (l, EApp (F <$> tr t x) (EVar (B ()))))
      (rowToList row)
      (sortWith fst flds)
    tr _ (EProj l (TT rt) r) = ELam (ttype tracetf) $ toScope $
      EProj l (TT (CApp tracetf rt))
      (EApp (F <$> tr rt r) (traceId tracetf))
    tr (CList nElementC) (EFor (TT mElementC) m n) = ELam (ttype tracetf) $ toScope $
      EFor (TT (CApp tracetf mElementC))
      (EApp (fmap F (tr (CList mElementC) m)) (traceId tracetf)) $ toScope $
      -- Right, so this fmap is where we keep the "same" variable that
      -- was bound in the body before.
      EApp (fmap (\v -> case v of F x -> F (F x); B () -> B ()) (trace' tracetf (F value) (TT (CList nElementC)) (fromScope n))) $
      ETLam KType $ ELam (TT (toScope (CApp (F <$> tracetf) (CVar (B ()))))) $ toScope $
      EApp (ETApp (EVar (F (F (B ())))) (toScope (CTrace (CVar (B ())))))
      (EVariant "For" (ERecord [("in", EVar (F (B ()))), ("out", EVar (B ()))]))
    tr c (EIf eCond eThen eElse) = ELam (ttype tracetf) $ toScope $
      EIf (EApp (ETApp (EVar (F value)) CBool) (tCondId F))
          (EApp (F <$> tr c eThen)
            (ETLam KType $ ELam (TT (toScope (CApp (F <$> tracetf) (CVar (B ()))))) $ toScope $
               EApp (ETApp (EVar (F (B ()))) (toScope (F <$> CApp tracetf c))) $
                    EVariant "IfThen" (ERecord [("cond", liftCE (tCondId (F . F))), ("then", EVar (B ()))])))
      (EApp (F <$> tr c eElse)
            (ETLam KType $ ELam (TT (toScope (CApp (F <$> tracetf) (CVar (B ()))))) $ toScope $
               EApp (ETApp (EVar (F (B ()))) (toScope (F <$> CApp tracetf c))) $
                    EVariant "IfElse" (ERecord [("cond", liftCE (tCondId (F . F))), ("else", EVar (B ()))])))
      where
        tCondId lifting = EApp (lifting <$> tr CBool eCond) (traceId tracetf)
    tr (CList (CRecord row)) (ETable n (TT (CRecord row'))) = assert (row == row') $
      ELam (ttype tracetf) $ toScope $
      EFor (TT (CApp tracetf (CRecord row')))
           (ETable n (TT (CRecord row'))) $ toScope $
           ESingletonList (ERecord (map fieldf (rowToList row)))
      where
        -- fieldf :: (Label, Constructor a) -> (Label, Expr Constructor a (Var () (Var () x)))
        fieldf (l, c) = (l, EApp (ETApp (EVar (F (B ()))) c)
                                 (EVariant "Row" (ERecord [("table", EString n), ("column", EString l), ("data", EProj l (TT (CRecord row')) (EVar (B ())))])))
    tr CBool (EEq (TT t) l r) = ELam (ttype tracetf) $ toScope $
      EApp (ETApp (EVar (B ())) CBool)
           (EVariant "OpEq" (ERecord [("left", EApp (F <$> tr t l) (traceId tracetf)),
                                      ("right", EApp (F <$> tr t r) (traceId tracetf))]))
trace' _ _ _ _ = error "trace called with non-TT(c) type"

trace :: Type Constructor String -> Expr Constructor String String -> Expr Constructor String String
trace = trace' (CVar "TRACE") "value"

putE :: Expr Constructor String String -> IO ()
putE e = do
  putDoc $ prettyExpr (evars, tvars) False e
  putStrLn ""

someFunc :: IO ()
someFunc = do
  {-
  let notTrue = EIf ETrue EFalse ETrue
  putE notTrue

  let constantFor = efor "x" (TT CBool) (ESingletonList ETrue) (ESingletonList ETrue)
  putE constantFor
  let simpleFor = efor "m" (TT (CVar "am")) (EVar "M") (EVar "N") --(ESingeltonList (EVar "m"))
  putE simpleFor

  -- putE $ betaReduceN 0 $ EApp (trace (TT (CList (CVar "an"))) simpleFor) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 1 $ EApp (trace (TT (CList (CVar "an"))) simpleFor) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 2 $ EApp (trace (TT (CList (CVar "an"))) simpleFor) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 3 $ EApp (trace (TT (CList (CVar "an"))) simpleFor) (traceId (CVar "TRACE"))
  putE $ betaReduceN 6 $ EApp (trace (TT (CList (CVar "an"))) simpleFor) (traceId (CVar "TRACE"))

  let forNestedBase = efor "a" (TT CBool) (ESingletonList ETrue) (efor "b" (TT CBool) (ESingletonList EFalse) (ESingletonList (EVar "y")))
  putE forNestedBase

  let forNested = efor "a" (TT CBool) (ESingletonList ETrue) (efor "b" (TT CBool) (ESingletonList EFalse) (ESingletonList (ERecord [("a", EVar "a"), ("b", EVar "b")])))
  putE forNested
  putE $ betaReduceN 11 $ EApp (trace (TT (CList (CRecord (CRowCons "a" CBool (CRowCons "b" CBool CRowNil))))) forNested) (traceId (CVar "TRACE"))

  let forIf = efor "x" (TT CBool) (EConcat (EVar "xs") (EVar "ys")) (EIf (EVar "x") (ESingletonList (EVar "x")) EEmptyList)
  putE forIf
  -- putE $ betaReduceN 0 $ EApp (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 1 $ EApp (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 2 $ EApp (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 3 $ EApp (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 4 $ EApp (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 5 $ EApp (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 6 $ EApp (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 7 $ EApp (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 8 $ EApp (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  putE $ betaReduceN 9 $ EApp (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  -}

  let record1 = ERecord [("b", ETrue), ("a", EFalse)]
  putE $ record1
  -- putE $ betaReduceN 0  $ EApp (trace (TT (CRecord (CRowCons "b" CBool (CRowCons "a" CBool CRowNil)))) record1) (traceId (CVar "TRACE"))
  putE $ betaReduceN 4 $ EApp (trace (TT (CRecord (CRowCons "b" CBool (CRowCons "a" CBool CRowNil)))) record1) (traceId (CVar "TRACE"))

  let recRec = ERecord [("a", ERecord [("b", ETrue)])]
  putE recRec
  putE $ betaReduceN 5 $ EApp (trace (TT (CRecord (CRowCons "a" (CRecord (CRowCons "b" CBool CRowNil)) CRowNil))) recRec) (traceId (CVar "TRACE"))

  let proj1 = EProj "b" (TT (CRecord (CRowCons "b" CBool (CRowCons "a" CBool CRowNil)))) record1
  putE $ proj1
  putE $ betaReduceN 7 $ EApp (trace (TT CBool) proj1) (traceId (CVar "TRACE"))

  let projRecRec = EProj "b" (TT (CRecord (CRowCons "b" CBool CRowNil))) (EProj "a" (TT (CRecord (CRowCons "a" (CRecord (CRowCons "b" CBool CRowNil)) CRowNil))) recRec)
  putE projRecRec
  putE $ betaReduceN 11 $ EApp (trace (TT CBool) projRecRec) (traceId (CVar "TRACE"))

  let crab = CRecord (CRowCons "a" CString (CRowCons "b" CBool CRowNil))

  let tableABs = ETable "abs" (TT crab)
  putE tableABs
  putE $ betaReduceN 3 $ EApp (trace (TT (CList crab)) tableABs) (traceId (CVar "TRACE"))

  let asFromTable = efor "x" (TT crab) tableABs (ESingletonList (EProj "a" (TT crab) (EVar "x")))
  putE asFromTable
  putE $ betaReduceN 6 $ EApp (trace (TT (CList CString)) asFromTable) (traceId (CVar "TRACE"))

  let selfJoin = efor "x" (TT crab) tableABs (efor "y" (TT crab) tableABs
                   (EIf (EEq (TT CString) (EProj "a" (TT crab) (EVar "x")) (EProj "a" (TT crab) (EVar "y")))
                        (ESingletonList (ERecord [("x", EVar "x"), ("y", EVar "y")]))
                        EEmptyList))
  putE selfJoin
  putE $ betaReduceN 17 $ EApp (trace (TT (CList (CRecord (CRowCons "x" crab (CRowCons "y" crab CRowNil))))) selfJoin) (traceId (CVar "TRACE"))

  let eqLists = EEq (TT (CList CString)) (ESingletonList (EString "a")) EEmptyList
  putE eqLists
  putE $ betaReduceN 6 $ EApp (trace (TT CBool) eqLists) (traceId (CVar "TRACE"))

  let eqEq = EEq (TT CBool) eqLists ETrue
  putE eqEq
  -- putE $ betaReduceN 2 $ EApp (trace (TT CBool) eqEq) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 4 $ EApp (trace (TT CBool) eqEq) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 6 $ EApp (trace (TT CBool) eqEq) (traceId (CVar "TRACE"))
  putE $ betaReduceN 8 $ EApp (trace (TT CBool) eqEq) (traceId (CVar "TRACE"))

{-  let projForNested = efor "x" (TT (CRecord (CRowCons "b" CBool (CRowCons "a" CBool CRowNil)))) forNested (ESingletonList (EProj "a" (TT (CRecord (CRowCons "a" CBool (CRowCons "b" CBool CRowNil)))) (EVar "x")))
  putE projForNested
  putE $ betaReduceN 12 $ EApp (trace (TT (CList CBool)) projForNested) (traceId (CVar "TRACE"))
  -- Fuck. Something is still wrong. Record projection, I think. Maybe I need RMAP?

  let proj2 = efor "x" (TT (CRecord (CRowCons "a" CBool CRowNil))) (ESingletonList (ERecord [("a", ETrue)])) (ESingletonList (EProj "a" (TT (CRecord (CRowCons "a" CBool CRowNil))) (EVar "x")))
  putE proj2
  -- putE $ betaReduceN 0 $ EApp (trace (TT (CList CBool)) proj2) (traceId (CVar "TRACE"))
  putE $ betaReduceN 10 $ EApp (trace (TT (CList CBool)) proj2) (traceId (CVar "TRACE"))

-}
