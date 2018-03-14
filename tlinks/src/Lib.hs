{-# LANGUAGE InstanceSigs, FlexibleContexts, DeriveFunctor, StandaloneDeriving, TemplateHaskell, RankNTypes, ScopedTypeVariables, TupleSections, LambdaCase #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Lib
    ( someFunc
    , clam
    , tforall
    , elam
    , etlam
    , efor
    , putC
    ) where

import Bound ((>>>=), Var(B,F))
import Bound.Scope.Simple
import Control.Exception (assert)
import GHC.Exts (sortWith)
import Control.Monad (ap)
import Control.Monad.Morph (lift, hoist)
import Data.Functor.Classes (Eq1)
import Data.Deriving (deriveShow1, deriveEq1)
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

data Kind = KType | KRow | KArrow Kind Kind
  deriving (Show, Eq)

prettyKind :: Kind -> Doc
prettyKind KType = text "Type"
prettyKind KRow = text "Row"
prettyKind (KArrow l r) = parens $ prettyKind l <+> text "->" <+> prettyKind r

type Label = String

data Constructor a
  = CBool
  | CInt
  | CString
  | CVar a {- Uhm. I'd quite like a type annotation on variables, but then how do I write `return`?! -}
  | CLam Kind (Scope () Constructor a)
  | CApp (Constructor a) (Constructor a)
  | CList (Constructor a)
  | CTrace (Constructor a)
  -- I don't really want another datatype for constructor rows
  | CRecord (Constructor a)
  | CRowNil
  | CRowCons Label (Constructor a) (Constructor a)
  | CTyperec (Constructor a) (Constructor a) (Constructor a) (Constructor a) (Constructor a) (Constructor a) (Constructor a)
  | CRMap (Constructor a) (Constructor a)
  deriving (Functor)

deriveEq1 ''Constructor
deriving instance Eq a => Eq (Constructor a)
deriveShow1 ''Constructor
deriving instance Show a => Show (Constructor a)

instance Applicative Constructor where
  pure = return
  (<*>) = ap

instance Monad Constructor where
  return = CVar

  CBool >>= _ = CBool
  CInt >>= _ = CInt
  CString >>= _ = CString
  CVar a >>= f = f a
  CLam k b >>= f = CLam k (b >>>= f)
  CApp a b >>= f = CApp (a >>= f) (b >>= f)
  CList a >>= f = CList (a >>= f)
  CTrace a >>= f = CTrace (a >>= f)
  CRecord r >>= f = CRecord (r >>= f)
  CRowNil >>= _ = CRowNil
  CRowCons l c r >>= f = CRowCons l (c >>= f) (r >>= f)
  CTyperec x b i s l r t >>= f = CTyperec (x >>= f) (b >>= f) (i >>= f) (s >>= f) (l >>= f) (r >>= f) (t >>= f)

clam :: Eq a => a -> Kind -> Constructor a -> Constructor a
clam a k b = CLam k (abstract1 a b)

prettyConstructor :: [String] -> Bool -> Constructor String -> Doc
prettyConstructor [] _ _ = error "ran out of type variables during constructor pretty printing"
-- TODO these might be needed for rowmap and stuff
prettyConstructor _ _ CRowNil = error "row outside of record"
prettyConstructor _ _ (CRowCons _ _ _) = error "row outside of record"
prettyConstructor _ _ CBool = text "Bool*"
prettyConstructor _ _ CInt = text "Int*"
prettyConstructor _ _ CString = text "String*"
prettyConstructor _ _ (CVar a) = text a
prettyConstructor (av:avs) p (CLam k body) = pparens p $ hang 2 $ group $
  bold (char 'λ') <> text av <> kindAnnotation <> char '.' <> {- P.<$$> -} prettyConstructor avs False (instantiate1 (CVar av) body)
  where kindAnnotation = case k of
          KType -> empty
          _ -> char ':' <> prettyKind k
prettyConstructor avs p (CApp a b) = pparens p $
  prettyConstructor avs True a <+> prettyConstructor avs True b
prettyConstructor avs p (CList a) = pparens p $ text "List*" <+> prettyConstructor avs True a
prettyConstructor avs p (CTrace a) = pparens p $ text "Trace*" <+> prettyConstructor avs True a
prettyConstructor _ p (CRecord (CVar x)) = pparens p $ text "Record*" <+> text x
prettyConstructor avs p (CRecord row) = pparens p $ text "Record*" <+> parens (prettyCRow avs row)
prettyConstructor avs p (CTyperec x b i s l r t) = pparens p $ bold (text "Typerec") <+> prettyConstructor avs True x </>
  tupled (map (prettyConstructor avs False) [b, i, s, l, r, t])

prettyCRow :: [String] -> Constructor String -> Doc
prettyCRow _ CRowNil = char '⋅'
prettyCRow avs (CRowCons l c CRowNil) =
  text l <> char ':' <+> prettyConstructor avs False c
prettyCRow avs (CRowCons l c r) =
  text l <> char ':' <+> prettyConstructor avs False c <> char ',' <+> prettyCRow avs r
prettyCRow _ (CVar x) = text x
prettyCRow _ _ = error "not a crow"

data Type c a
  = TBool | TInt | TString
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
    go _ _ TInt = TInt
    go _ _ TString = TString
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
prettyType _ _ TInt = text "Int"
prettyType _ _ TString = text "String"
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
    go _ _ TInt = TInt
    go _ _ TString = TString
    go f a (TT c) = TT (f a c)
    go f a (TForall k b) = TForall k (go f' a b)
      where
        f' v = Scope . f (fmap F v) . unscope
    go f a (TArrow l r) = TArrow (go f a l) (go f a r)
    go f a (TList t) = TList (go f a t)
    go f a (TTrace t) = TTrace (go f a t)

data Trace c a x
  = TrLit (Expr c a x)
  | TrFor (c a) (Expr c a x)
  | TrEq (c a) (Expr c a x)
  deriving (Functor)

data Expr c a x
  = EUndefined
  | ETrue | EFalse
  | EString String
  | EVar x
  | EIf (Expr c a x) (Expr c a x) (Expr c a x)
  | ELam (Type c a) (Scope () (Expr c a) x)
  | EFix (Type c a) (Scope () (Expr c a) x)
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
  -- The Type is the type of the record
  | ERmap (Expr c a x) (Type c a) (Expr c a x)
  -- the Type is the type of the record. I need this for tracing.
  | EProj Label (Type c a) (Expr c a x)
  | ETable String (Type c a) -- type of ELEMENTS/ROWS that is, a record type, not a list type
  | EEq (Type c a) (Expr c a x) (Expr c a x) -- equality specialized to a type
  | ETypecase (c a) (Expr c a x) (Expr c a x) (Expr c a x) (Expr (Scope () c) a x) (Expr (Scope () c) a x) (Expr (Scope () c) a x)
  | ETrace (Trace c a x)
  | ETracecase (Expr c a x) -- discriminant
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
  return = EVar

  EUndefined >>= _ = EUndefined
  ETrue >>= _ = ETrue
  EFalse >>= _ = EFalse
  EString s >>= _ = EString s
  EVar x >>= f = f x
  EFix t b >>= f = EFix t (b >>>= f)
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
  ERmap a t b >>= f = ERmap (a >>= f) t (b >>= f)
  EIf i t e >>= f = EIf (i >>= f) (t >>= f) (e >>= f)
  EProj l t e >>= f = EProj l t (e >>= f)
  ETable n t >>= _ = ETable n t
  EEq t l r >>= f = EEq t (l >>= f) (r >>= f)
  ETypecase c b i s l r t >>= f = ETypecase c (b >>= f) (i >>= f) (s >>= f) (l >>= liftCE . f) (r >>= liftCE . f) (t >>= liftCE . f)
  ETracecase x l t e g r q >>= f =
    ETracecase (x >>= f) (l >>>= f) (t >>>= f) (e >>>= f) (g >>>= liftCE . f) (r >>>= f) (q >>>= liftCE . f)
  ETrace (TrFor c e) >>= f = ETrace (TrFor c (e >>= f))
  ETrace (TrEq c e) >>= f = ETrace (TrEq c (e >>= f))

liftCE :: Monad c => Expr c a b -> Expr (Scope () c) a b
liftCE EUndefined = EUndefined
liftCE ETrue = ETrue
liftCE EFalse = EFalse
liftCE (EString s) = EString s
liftCE (EVar x) = EVar x
liftCE (EFix t b) = EFix (liftCT t) (hoistScope liftCE b)
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
liftCE (ERmap a t b) = ERmap (liftCE a) (liftCT t) (liftCE b)
liftCE (EProj l t e) = EProj l (liftCT t) (liftCE e)
liftCE (ETable n t) = ETable n (liftCT t)
liftCE (EEq t l r) = EEq (liftCT t) (liftCE l) (liftCE r)
liftCE (ETypecase c b i s l r t) = ETypecase (lift c) (liftCE b) (liftCE i) (liftCE s) (liftCE l) (liftCE r) (liftCE t)
liftCE (ETracecase x l it ie f r oe) = ETracecase
  (liftCE x)
  (hoistScope liftCE l)
  (hoistScope liftCE it)
  (hoistScope liftCE ie)
  (hoistScope liftCE f)
  (hoistScope liftCE r)
  (hoistScope liftCE oe)
liftCE (ETrace (TrLit e)) = ETrace (TrLit (liftCE e))
liftCE (ETrace (TrFor c e)) = ETrace (TrFor (lift c) (liftCE e))
liftCE (ETrace (TrEq c e)) = ETrace (TrEq (lift c) (liftCE e))

liftCT :: Monad c => Type c a -> Type (Scope () c) a
liftCT TBool = TBool
liftCT TInt = TInt
liftCT TString = TString
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
eInstantiateC1 _ EUndefined = EUndefined
eInstantiateC1 _ ETrue = ETrue
eInstantiateC1 _ EFalse = EFalse
eInstantiateC1 _ (EString s) = EString s
eInstantiateC1 _ (EVar x) = EVar x
eInstantiateC1 a (ELam t b) = ELam (tInstantiate1 a t) (hoistScope (eInstantiateC1 a) b)
eInstantiateC1 a (EFix t b) = EFix (tInstantiate1 a t) (hoistScope (eInstantiateC1 a) b)
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
eInstantiateC1 a (ERmap x t y) = ERmap (eInstantiateC1 a x) (tInstantiate1 a t) (eInstantiateC1 a y)
eInstantiateC1 a (EProj l t e) = EProj l (tInstantiate1 a t) (eInstantiateC1 a e)
eInstantiateC1 a (ETable n t) = ETable n (tInstantiate1 a t)
eInstantiateC1 a (EEq t l r) = EEq (tInstantiate1 a t) (eInstantiateC1 a l) (eInstantiateC1 a r)
eInstantiateC1 a (ETypecase c b i s l r t) = ETypecase (instantiate1 a c) (eInstantiateC1 a b) (eInstantiateC1 a i) (eInstantiateC1 a s) (eInstantiateC1 (lift a) l) (eInstantiateC1 (lift a) r) (eInstantiateC1 (lift a) t)
eInstantiateC1 a (ETracecase x l it ie f r oe) = ETracecase
  (eInstantiateC1 a x)
  (hoistScope (eInstantiateC1 a) l)
  (hoistScope (eInstantiateC1 a) it)
  (hoistScope (eInstantiateC1 a) ie)
  (hoistScope (eInstantiateC1 (lift a)) f)
  (hoistScope (eInstantiateC1 a) r)
  (hoistScope (eInstantiateC1 (lift a)) oe)
eInstantiateC1 a (ETrace (TrLit e)) = ETrace (TrLit (eInstantiateC1 a e))
eInstantiateC1 a (ETrace (TrFor c e)) = ETrace (TrFor (instantiate1 a c) (eInstantiateC1 a e))
eInstantiateC1 a (ETrace (TrEq c e)) = ETrace (TrEq (instantiate1 a c) (eInstantiateC1 a e))

-- abstract over a constructor in an expression
eAbstractC1 :: Eq a => Functor c => a -> Expr c a x -> Expr (Scope () c) a x
eAbstractC1 _ ETrue = ETrue
eAbstractC1 _ EFalse = EFalse
eAbstractC1 _ (EString s) = EString s
eAbstractC1 _ (EVar x) = EVar x
eAbstractC1 a (ELam t b) = ELam (tAbstract1 a t) (hoistScope (eAbstractC1 a) b)
eAbstractC1 a (EFix t b) = EFix (tAbstract1 a t) (hoistScope (eAbstractC1 a) b)
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
eAbstractC1 a (ETypecase c b i s l r t) = ETypecase (abstract1 a c) (eAbstractC1 a b) (eAbstractC1 a i) (eAbstractC1 a s) (eAbstractC1 a l) (eAbstractC1 a r) (eAbstractC1 a t)

etlam :: Eq a => Monad c => a -> Kind -> Expr c a x -> Expr c a x
etlam a k b = ETLam k (eAbstractC1 a b) -- this should be actual abstract, not my misnamed one, I think

-- the TRACE type function
tracetf :: Constructor a
tracetf = CLam KType $ toScope $ CTyperec (CVar (B ()))
  (CTrace CBool) (CTrace CInt) (CTrace CString)
  (CLam KType (toScope (CLam KType (toScope (CList (CVar (B ())))))))
  (CLam KRow (toScope (CLam KRow (toScope (CRecord (CVar (B ())))))))
  (CLam KType (toScope (CLam KType (toScope (CTrace (CVar (B ())))))))

-- the VALUE type function
valuetf :: Constructor a
valuetf = CLam KType $ toScope $ CTyperec (CVar (B ()))
  CBool CInt CString
  (CLam KType (toScope (CLam KType (toScope (CList (CVar (B ())))))))
  (CLam KRow (toScope (CLam KRow (toScope (CRecord (CVar (B ())))))))
  (CLam KType (toScope (CLam KType (toScope (CVar (B ()))))))

-- the value trace analysis function
value :: Eq a => Expr Constructor a x
value = EFix (TForall KType (TArrow
                              (TT $ toScope $ CVar (B ()))
                              (TT $ toScope $ CApp valuetf (CVar (B ()))))) $ toScope $ ETLam KType $ ETypecase (toScope (CVar (B ())))
        -- Bool
        (ELam (TT (lift CBool)) (toScope (EVar (B ()))))
        -- Int
        (ELam (TT (lift CInt)) (toScope (EVar (B ()))))
        -- String
        (ELam (TT (lift CString)) (toScope (EVar (B ()))))
        -- List
        (ELam (TT (lift (toScope (CList (CVar (B ())))))) -- (toScope (toScope (CList (CVar (B ()))))))
          (toScope (EFor (TT (toScope (toScope (CVar (B ())))))
                     (EVar (B ()))
                     (toScope (ESingletonList (EApp (ETApp (EVar (F (F (B ())))) (toScope (toScope (CVar (B ()))))) (EVar (B ()))))))))
        -- Record
        (ELam (TT (toScope (toScope (CRecord (CVar (B ()))))))
          (toScope (ERmap (EVar (F (B ()))) (TT (toScope (toScope (CRecord (CVar (B ())))))) (EVar (B ())))))
        -- Trace
        (ELam (TT (toScope (toScope (CTrace (CVar (B ()))))))
         (toScope (ETracecase (EVar (B ()))
                   -- Lit
                   (toScope (EVar (B ())))
                   -- IfThen
                   (toScope (EApp (ETApp (EVar (F (F (B ())))) (toScope (toScope (CTrace (CVar (B ()))))))
                              (EProj "then" (TT (toScope (toScope (CRecord (CRowCons "then" (CTrace (CVar (B ()))) (CRowCons "cond" (CTrace CBool) CRowNil)))))) (EVar (B ())))))
                   -- IfElse
                   (toScope (EApp (ETApp (EVar (F (F (B ())))) (toScope (toScope (CTrace (CVar (B ()))))))
                              (EProj "else" (TT (toScope (toScope (CRecord (CRowCons "else" (CTrace (CVar (B ()))) (CRowCons "cond" (CTrace CBool) CRowNil)))))) (EVar (B ())))))
                   -- For
                   (toScope (EApp (ETApp (EVar (F (F (B ())))) (toScope (toScope (toScope (CTrace (CVar (F (B ()))))))))
                             (EProj "out" (TT (toScope (toScope (toScope (CRecord CRowNil {- TODO -})))))
                              (EVar (B ())))))
                   -- Row
                   (toScope (EProj "data" (TT (toScope (toScope (CRecord (CRowCons "data" (CVar (B ())) {- TODO other fields -} CRowNil)))))
                             (EVar (B ()))))
                   -- OpEq
                   (toScope (EEq (TT (toScope (toScope (toScope (CVar (B ()))))))
                             (EApp (ETApp (EVar (F (F (B ())))) (toScope (toScope (toScope (CTrace (CVar (B ())))))))
                               (EProj "left" eqRType (EVar (B ()))))
                             (EApp (ETApp (EVar (F (F (B ())))) (toScope (toScope (toScope (CTrace (CVar (B ())))))))
                               (EProj "right" eqRType (EVar (B ()))))))
                   )))
        where
          eqRType = TT (toScope (toScope (toScope (CRecord (CRowCons "left" (CTrace (CVar (B ()))) (CRowCons "right" (CTrace (CVar (B ()))) CRowNil))))))

traceId :: Expr Constructor a x
traceId = ETLam KType $ ELam (TT $ toScope (CApp (F <$> tracetf) (CVar (B ())))) $ toScope (EVar (B ()))

isApp :: Expr c a x -> Bool
isApp (EApp _ _) = True
isApp (ETApp _ _) = True
isApp _ = False

prettyExpr :: ([String], [String]) -> Bool -> Expr Constructor String String -> Doc
prettyExpr ([], _) _ _ = error "ran out of variable names"
prettyExpr (_, []) _ _ = error "ran out of type variable names"
prettyExpr _ _ EUndefined = red (char '⊥')
prettyExpr _ _ ETrue = text "true"
prettyExpr _ _ EFalse = text "false"
prettyExpr _ _ (EVar x) = text x
prettyExpr _ _ (EString s) = text (show s)
prettyExpr (v:vs, tvs) p (EFix t e) = pparens p $ hang 2 $ group $
  bold (text "fix") <+> parens (text v <> colon <> prettyType tvs False t) <> dot P.<$$> prettyExpr (vs, tvs) False (instantiate1 (EVar v) e)
prettyExpr (v:vs, tvs) p (ELam t b) = pparens p $ hang 2 $ group $
  bold (char 'λ') <> text v <> typeAnnotation <> char '.' P.<$$> prettyExpr (vs, tvs) False (instantiate1 (EVar v) b)
  where typeAnnotation = char ':' <> prettyType tvs False t
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
  bold (text "for") <+> (hang 3 (parens (text v <> typeAnnotation <+> text "<-" <+> prettyExpr (v:vs, tvs) False i))) P.<$> prettyExpr (vs, tvs) False (instantiate1 (EVar v) o)
  where typeAnnotation = char ':' <+> prettyType tvs False t
prettyExpr _ _ (ERecord []) = braces empty
prettyExpr ns _ (ERecord l) = group $ braces $ align (cat (punctuate (comma <> space) (map (\(lbl, e) -> blue (text lbl) <+> char '=' <+> prettyExpr ns False e) l)))
prettyExpr ns p (EIf c t e) = pparens p $ group $
  bold (text "if") <+> prettyExpr ns False c P.<$>
  bold (text "then") <+> prettyExpr ns False t P.<$>
  bold (text "else") <+> prettyExpr ns False e
prettyExpr ns _ (EProj l _t e) = parens $
  prettyExpr ns True e <> char '.' <> blue (text l)
prettyExpr (_, tvs) p (ETable n t) = pparens p $
  bold (text "table") <+> text (show n) <+> prettyType tvs True t
prettyExpr (ns, tv:tvs) p (ETypecase c b i s l r t) = pparens p $
  bold (text "typecase") <+> prettyConstructor (tv:tvs) False c <+> bold (text "of") <$$>
  (indent 2 $
    text "Bool => " <> prettyExpr (ns, tv:tvs) False b <$$>
    text "Int => " <> prettyExpr (ns, tv:tvs) False i <$$>
    text "String => " <> prettyExpr (ns, tv:tvs) False s <$$>
    text "List " <> text tv <> text " => " <> prettyExpr (ns, tvs) False (eInstantiateC1 (CVar tv) l) <$$>
    text "Record " <> text tv <> text " => " <> prettyExpr (ns, tvs) False (eInstantiateC1 (CVar tv) r) <$$>
    text "Trace " <> text tv <> text " => " <> prettyExpr (ns, tvs) False (eInstantiateC1 (CVar tv) t))
prettyExpr ns p (ERmap f _t r) = pparens p $
  bold (text "rmap") <+> prettyExpr ns True f <+> prettyExpr ns True r
prettyExpr (v:vs, tv:tvs) p (ETracecase x l it ie f r oe) = pparens p $
  bold (text "tracecase") <+> prettyExpr (v:vs, tv:tvs) False x <+> bold (text "of") <$$>
  (indent 2 $
    text "Lit" <+> text v <+> text "=>" <+> prettyExpr (vs, tv:tvs) False (instantiate1 (EVar v) l) <$$>
    text "IfThen" <+> text v <+> text "=>" <+> prettyExpr (vs, tv:tvs) False (instantiate1 (EVar v) it) <$$>
    text "IfElse" <+> text v <+> text "=>" <+> prettyExpr (vs, tv:tvs) False (instantiate1 (EVar v) ie) <$$>
    text "For" <+> text tv <+> text v <+> text "=>" <+> prettyExpr (vs, tvs) False (eInstantiateC1 (CVar tv) (instantiate1 (EVar v) f)) <$$>
    text "Row" <+> text v <+> text "=>" <+> prettyExpr (vs, tv:tvs) False (instantiate1 (EVar v) r) <$$>
    text "Op==" <+> text tv <+> text v <+> text "=>" <+> prettyExpr (vs, tvs) False (eInstantiateC1 (CVar tv) (instantiate1 (EVar v) oe)))
prettyExpr ns p (ETrace (TrLit e)) = pparens p $ green (text "Lit") <+> prettyExpr ns True e
prettyExpr ns@(_, tvs) p (ETrace (TrFor c e)) = pparens p $ green (text "For") <+> prettyConstructor tvs True c <+> prettyExpr ns True e
prettyExpr ns@(_, tvs) p (ETrace (TrEq c e)) = pparens p $ green (text "Eq") <+> prettyConstructor tvs True c <+> prettyExpr ns True e


betaReduce :: Eq a => Monad c => Expr c a x -> Expr c a x
betaReduce EUndefined = EUndefined
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


rowToList :: Constructor a -> [(Label, Constructor a)]
rowToList = sortWith fst . rowToList'
  where
    rowToList' CRowNil = []
    rowToList' (CRowCons l c r) = (l, c) : rowToList' r
    rowToList' _ = error "not a row"

ttype :: Constructor a -> Type Constructor a
ttype _ = TForall KType $
  TArrow (TT $ toScope $ CApp (fmap F tracetf) (CVar (B ())))
         (TT $ toScope $ CApp (fmap F tracetf) (CVar (B ())))

trace' :: Eq a => Type Constructor a -> Expr Constructor a x -> Expr Constructor a x
trace' _ (ELam _ _) = error "cannot trace lambda"
trace' _ (ETLam _ _) = error "cannot trace Lambda"
trace' _ (EApp _ _) = error "cannot trace app"
trace' _ (EVariant _ _) = error "cannot trace variant constructor"
trace' (TT constructor) expression = tr constructor expression
  where
    tr CBool ETrue = ELam (ttype tracetf) $ toScope $
      EApp (ETApp (EVar (B ())) CBool) (ETrace (TrLit ETrue)) -- (EVariant "Lit" ETrue)
    tr CBool EFalse = ELam (ttype tracetf) $ toScope $
      EApp (ETApp (EVar (B ())) CBool) (ETrace (TrLit EFalse)) -- (EVariant "Lit" EFalse)
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
      (EApp (F <$> tr rt r) traceId)
    tr (CList nElementC) (EFor (TT mElementC) m n) = ELam (ttype tracetf) $ toScope $
      EFor (TT (CApp tracetf mElementC))
      (EApp (fmap F (tr (CList mElementC) m)) traceId) $ toScope $
      -- Right, so this fmap is where we keep the "same" variable that
      -- was bound in the body before.
      EApp (fmap (\v -> case v of F x -> F (F x); B () -> B ()) (trace' (TT (CList nElementC)) (fromScope n))) $
      ETLam KType $ ELam (TT (toScope (CApp (F <$> tracetf) (CVar (B ()))))) $ toScope $
      EApp (ETApp (EVar (F (F (B ())))) (toScope (CTrace (CVar (B ())))))
      (ETrace (TrFor (toScope (F <$> mElementC)) (ERecord [("in", EVar (F (B ()))), ("out", EVar (B ()))])))
    tr c (EIf eCond eThen eElse) = ELam (ttype tracetf) $ toScope $
      EIf (EApp (ETApp value (CTrace CBool)) (tCondId F))
          (EApp (F <$> tr c eThen)
            (ETLam KType $ ELam (TT (toScope (CApp (F <$> tracetf) (CVar (B ()))))) $ toScope $
               EApp (ETApp (EVar (F (B ()))) (toScope (F <$> CApp tracetf c))) $
                    EVariant "IfThen" (ERecord [("cond", liftCE (tCondId (F . F))), ("then", EVar (B ()))])))
      (EApp (F <$> tr c eElse)
            (ETLam KType $ ELam (TT (toScope (CApp (F <$> tracetf) (CVar (B ()))))) $ toScope $
               EApp (ETApp (EVar (F (B ()))) (toScope (F <$> CApp tracetf c))) $
                    EVariant "IfElse" (ERecord [("cond", liftCE (tCondId (F . F))), ("else", EVar (B ()))])))
      where
        tCondId lifting = EApp (lifting <$> tr CBool eCond) traceId
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
      (ETrace (TrEq t
                (ERecord [("left", EApp (F <$> tr t l) traceId),
                          ("right", EApp (F <$> tr t r) traceId)])))
trace' _ _ = error "trace called with non-TT(c) type"

trace :: Type Constructor String -> Expr Constructor String String -> Expr Constructor String String
trace = trace' -- "value"

unroll :: Eq a => Monad c => Int -> Expr c a x -> Expr c a x
unroll 0 (EFix _ _) = EUndefined
unroll n (EFix t b) = unroll (n-1) (instantiate1 (EFix t b) b)
unroll n EUndefined = EUndefined
unroll n ETrue = ETrue
unroll n EFalse = EFalse
unroll n (EString s) = EString s
unroll n (EVar x) = EVar x
unroll n (EIf c t e) = EIf (unroll n c) (unroll n t) (unroll n e)
unroll n (ELam t b) = ELam t (hoistScope (unroll n) b)
unroll n (EApp a b) = EApp (unroll n a) (unroll n b)
unroll n (ETLam k b) = ETLam k (unroll n b)
unroll n (ETApp e c) = ETApp (unroll n e) c
unroll n (EVariant l e) = EVariant l (unroll n e)
unroll n EEmptyList = EEmptyList
unroll n (ESingletonList e) = ESingletonList (unroll n e)
unroll n (EConcat l r) = EConcat (unroll n l) (unroll n r)
unroll n (EFor t i o) = EFor t (unroll n i) (hoistScope (unroll n) o)
unroll n (ERecord l) = ERecord (mapSnd (unroll n) l)
unroll n (EProj l t e) = EProj l t (unroll n e)
unroll n (ETable name t) = ETable name t
unroll n (ERmap a t b) = ERmap (unroll n a) t (unroll n b)
unroll n (EEq t l r) = EEq t (unroll n l) (unroll n r)
unroll n (ETypecase c b i s l r t) = ETypecase c (unroll n b) (unroll n i) (unroll n s) (unroll n l) (unroll n r) (unroll n t)
unroll n (ETracecase x l it ie f r oe) = ETracecase
  (unroll n x)
  (hoistScope (unroll n) l)
  (hoistScope (unroll n) it)
  (hoistScope (unroll n) ie)
  (hoistScope (unroll n) f)
  (hoistScope (unroll n) r)
  (hoistScope (unroll n) oe)
unroll n (ETrace (TrLit e)) = ETrace (TrLit (unroll n e))
unroll n (ETrace (TrFor c e)) = ETrace (TrFor c (unroll n e))
unroll n (ETrace (TrEq c e)) = ETrace (TrEq c (unroll n e))


one :: Show a => Eq a => Expr Constructor a x -> Expr Constructor a x
one EUndefined = EUndefined
one ETrue = ETrue
one EFalse = EFalse
one (EString s) = EString s
one (EVar v) = EVar v
one (EIf ETrue t _) = t
one (EIf EFalse _ e) = e
one (EIf c t e) = EIf (one c) (one t) (one e)
one (EApp (ELam _ b) a) = instantiate1 a b
one (EApp a b) = EApp (one a) (one b) -- one b is not necessary, but helps finding bugs
one (ELam t b) = ELam t (hoistScope one b) -- for debugging only
one l@ELam{} = l -- do not normalize under lambda
one (EFix _ _) = error "Unexpected fix"
one (ETLam _ _) = error "TODO Lambda"
one (ETApp (ETLam _ b) c) = eInstantiateC1 c b
one (ETApp a c) = ETApp (one a) c
one (ETable n t) = ETable n t
one (EVariant l e) = EVariant l (one e)
one EEmptyList = EEmptyList
one (ESingletonList e) = ESingletonList (one e)
one (EConcat EEmptyList r) = r
one (EConcat l EEmptyList) = l
one (EConcat l r) = EConcat (one l) (one r)
one (EFor _ EEmptyList _) = EEmptyList
one (EFor _ (ESingletonList e) o) = instantiate1 e o
-- for (x <- for (y <- L) M) N ~> for (y <- L) (for (x <- M) N)
-- This circumvents the safety implied by the Scope scope safety, but
-- should be correct. Variables in L stay unchanged. y is visible in
-- M, bound by the preceding for. The nesting looks different in
-- source code, but the binding structure is the same. On the left
-- side, x is visible in N, bound by the outer for. On the right side,
-- x is visible in N, bound by the outer for, so that stays the same.
-- On the right side, y is visible in N, but not used. However, all
-- other free variables need to move up one binder to account for y.
one (EFor xt (EFor yt l (Scope m)) n) =
  EFor yt l (Scope (EFor xt m (F <$> n)))
-- no, no, need proper elim frames
-- one (EFor t (EVar x) o) = EFor t (EVar x) (hoistScope one o) -- for debugging only

-- -- without eta expansion of tables:
-- one (EFor t (ETable n tt@(TT (CRecord row))) o) = EFor t (ETable n tt) (hoistScope one o)
-- -- with eta expansion of tables:
one (EFor t (ETable n tt@(TT (CRecord row))) o) = EFor t (ETable n tt) (hoistScope one etaO)
  where
    etaO = toScope $ ERecord (map (\(l, c) -> (l, EProj l tt (EVar (B ())))) (rowToList row))
one (EFor t i o) = EFor t (one i) o --(hoistScope one o)
one (ERecord fs) = ERecord (mapSnd one fs)
one (ERmap f (TT (CRecord row)) r) = ERecord
  (map (\(l,t) -> (l, EApp (ETApp f t) (EProj l (TT (CRecord row)) r)))
    (rowToList row))
one (ERmap _ _ _) = error "TODO need to normalize type (and switch to constructor, not type to begin with, I think"
one (EProj l _ (ERecord fs)) = case lookup l fs of
  Nothing -> error "label not found in record"
  Just e -> e
one (EProj l t e) = EProj l t (one e)
-- one (EEq _ l r) | l == r = ETrue --
one (EEq t l r) = EEq t (one l) (one r)
one (ETypecase c b i s l r t) = case c of
  CBool -> b; CInt -> i; CString -> s;
  CList c' -> eInstantiateC1 c' l
  CRecord c' -> eInstantiateC1 c' r
  CTrace c' -> eInstantiateC1 c' t
  _ -> ETypecase (normC c) b i s l r t
one (ETracecase x l it ie f r oe) = case x of
  ETrace (TrLit t) -> instantiate1 t l
  EVariant "Lit" t -> instantiate1 t l
  EVariant "IfThen" t -> instantiate1 t it
  EVariant "IfElse" t -> instantiate1 t ie
  EVariant "Row" t -> instantiate1 t r
  ETrace (TrFor c t) -> instantiate1 t (hoistScope (eInstantiateC1 c) f)
  ETrace (TrEq c t) -> instantiate1 t (hoistScope (eInstantiateC1 c) oe)
  EVariant l' _ -> error $ "unexpected label " ++ l' 
  x' -> ETracecase (one x') l it ie f r oe
  -- EVariant "For" t -> _ f -- TODO
one (ETrace (TrLit e)) = ETrace (TrLit (one e))
one (ETrace (TrFor c e)) = ETrace (TrFor c (one e))
one (ETrace (TrEq c e)) = ETrace (TrEq c (one e)) -- could normalize constructors, but not necessary

{-
wtf :: Expr c a x -> String
wtf EVar{} = "EVar"
wtf EUndefined{} = "EUndefined"
wtf ETrue = "ETrue"
wtf EFalse = "EFalse"
wtf (EString s) = "EString " ++ s
wtf EIf{} = "EIf"
wtf ELam{} = "ELam"
wtf EFix{} = "EFix"
wtf (EApp a b) = "EApp (" ++ wtf a ++ ") (" ++ wtf b ++ ")"
            -- (ETLam _ _)
            -- (ETApp _ _)
            -- (EVariant _ _)
            -- EEmptyList
-}

normC :: Show a => Eq a => Constructor a -> Constructor a
normC CBool = CBool
normC CInt = CInt
normC CString = CString
normC (CVar v) = CVar v
normC (CLam k b) = CLam k b -- can't normalize under binder, because .. why?
normC (CApp f a) = case normC f of
  (CLam _ b) -> normC $ instantiate1 a b
  e -> error $ "trying to apply non-type function " ++ show e
normC (CList c) = CList (normC c)
normC (CTrace c) = CTrace (normC c)
normC (CRecord c) = CRecord (normC c)
normC CRowNil = CRowNil
normC (CRowCons l c r) = CRowCons l (normC c) (normC r)
normC (CTyperec x b i s l r t) = normC $ case normC x of
  CBool -> b; CInt -> i; CString -> s
  CList c -> CApp (CApp l c) (CTyperec c b i s l r t)
  CRecord c -> CApp (CApp r c) (CRMap (CLam KType (toScope (CTyperec (CVar (B ())) (F <$> b) (F <$> i) (F <$> s) (F <$> l) (F <$> r) (F <$> t)))) c)
  CTrace c -> CApp (CApp t c) (CTyperec c b i s l r t)
  stuck -> error $ show stuck-- CTyperec stuck b i s l r t
normC (CRMap _ CRowNil) = CRowNil
normC (CRMap f (CRowCons l c r)) = normC $ CRowCons l (CApp f c) (CRMap f r)
normC (CRMap _ e) = error $ "Can't RowMap over " ++ show e

putE :: Expr Constructor String String -> IO ()
putE e = do
  putDoc $ prettyExpr (evars, tvars) False e
  putStrLn ""

putC :: Constructor String -> IO ()
putC c = do
  putDoc $ prettyConstructor tvars False c
  putStrLn ""

someFunc :: IO ()
someFunc = do
  -- putStrLn "TRACE:"
  -- putDoc $ prettyConstructor tvars False tracetf
  -- putStrLn ""
  -- putStrLn "VALUE:"
  -- putDoc $ prettyConstructor tvars False valuetf
  -- putStrLn ""

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

  let record1 = ERecord [("b", ETrue), ("a", EFalse)]
  putE $ record1
  -- putE $ betaReduceN 0  $ EApp (trace (TT (CRecord (CRowCons "b" CBool (CRowCons "a" CBool CRowNil)))) record1) (traceId (CVar "TRACE"))
  putE $ betaReduceN 4 $ EApp (trace (TT (CRecord (CRowCons "b" CBool (CRowCons "a" CBool CRowNil)))) record1) traceId

  let recRec = ERecord [("a", ERecord [("b", ETrue)])]
  putE recRec
  putE $ betaReduceN 5 $ EApp (trace (TT (CRecord (CRowCons "a" (CRecord (CRowCons "b" CBool CRowNil)) CRowNil))) recRec) traceId

  let proj1 = EProj "b" (TT (CRecord (CRowCons "b" CBool (CRowCons "a" CBool CRowNil)))) record1
  putE $ proj1
  putE $ betaReduceN 7 $ EApp (trace (TT CBool) proj1) traceId

  let projRecRec = EProj "b" (TT (CRecord (CRowCons "b" CBool CRowNil))) (EProj "a" (TT (CRecord (CRowCons "a" (CRecord (CRowCons "b" CBool CRowNil)) CRowNil))) recRec)
  putE projRecRec
  putE $ betaReduceN 11 $ EApp (trace (TT CBool) projRecRec) traceId
  -}
  putE $ value

  let crab = CRecord (CRowCons "a" CString (CRowCons "b" CBool CRowNil))

  let tableABs = ETable "abs" (TT crab)
  -- putE tableABs
  -- putE $ betaReduceN 3 $ EApp (trace (TT (CList crab)) tableABs) traceId

  let asFromTable = efor "x" (TT crab) tableABs (ESingletonList (EProj "a" (TT crab) (EVar "x")))
  -- putE asFromTable
  -- putE $ betaReduceN 6 $ EApp (trace (TT (CList CString)) asFromTable) traceId

  let selfJoin = efor "x" (TT crab) tableABs (efor "y" (TT crab) tableABs
                   (EIf (EEq (TT CString) (EProj "a" (TT crab) (EVar "x")) (EProj "a" (TT crab) (EVar "y")))
                        (ESingletonList (ERecord [("x", EVar "x"), ("y", EVar "y")]))
                        EEmptyList))
  -- putE selfJoin
  -- putE $ betaReduceN 17 $ EApp (trace (TT (CList (CRecord (CRowCons "x" crab (CRowCons "y" crab CRowNil))))) selfJoin) traceId
  -- putE $ ((!! 18) . iterate one) $ unroll 1 $ EApp (trace (TT (CList (CRecord (CRowCons "x" crab (CRowCons "y" crab CRowNil))))) selfJoin) (ETApp value (CApp tracetf (CList (CRecord (CRowCons "x" crab (CRowCons "y" crab CRowNil))))))

  let tAsFromTable = EApp (ETApp value (CList (CTrace CString)))
                          (EApp (trace (TT (CList CString)) asFromTable) traceId)
  putE $ asFromTable
  putStrLn "-------------------------------------------------------------------------------"
  putE $ ((!! 17) . iterate one) $ unroll 2 $ tAsFromTable
  putStrLn "------------------------"
  putE $  EApp (trace (TT (CList CString)) asFromTable) traceId


  -- let xFromTable = efor "x" (TT crab) tableABs (ESingletonList (EVar "x"))
  -- putE $ xFromTable
  -- let tXFromTable = EApp (trace (TT (CList crab)) xFromTable) traceId
  -- putE $ ((!! 11) . iterate one) $ unroll 0 $ tXFromTable
  -- let valueTXFromTable = ETApp value (CApp tracetf (CList crab))
  -- putE $ ((!! 9) . iterate one) $ unroll 2 $ valueTXFromTable
  -- putE $ ((!! 100) . iterate one) $ unroll 3 $ valueTXFromTable
  -- let unTTXFromTable = EApp valueTXFromTable tXFromTable
  -- putE $ ((!! 200) . iterate one) $ unroll 4 $ unTTXFromTable
  -- let tXFromTable = EApp (ETApp value (CApp tracetf (CList crab)))
  --                        
  -- putE $ tXFromTable
  -- putE $ ((!! 16) . iterate one) $ unroll 2 $ tXFromTable

  -- putE $ EApp (trace (TT (CList crab)) tableABs) traceId
  -- putE $ ((!! 3) . iterate one) $ EApp (trace (TT (CList crab)) tableABs) traceId
  -- putC (CList (CRecord (CRowCons "a" (CTrace CString) (CRowCons "b" (CTrace CBool) CRowNil))))
  -- putC (CApp tracetf (CList crab))
  -- putC (normC (CApp tracetf (CList crab)))

  

  -- let forfor = elam "foo" TBool $ efor "x" TBool (efor "y" TBool (EVar "L") (EApp (EVar "M") (EVar "y"))) (EApp (EApp (EVar "N") (EVar "x")) (EVar "foo"))
  -- putE forfor
  -- putE $ one $ forfor

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


  -- let valBool = EApp (ETApp value (CTrace CBool)) (ETrace (TrLit ETrue)) --(EVariant "Lit" ETrue)
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
