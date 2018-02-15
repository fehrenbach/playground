{-# LANGUAGE InstanceSigs, FlexibleContexts, DeriveFunctor, StandaloneDeriving, TemplateHaskell, RankNTypes, ScopedTypeVariables #-}
module Lib
    ( someFunc
    ) where

import Bound ((>>>=), Var(B,F))
import Bound.Scope.Simple
import Control.Monad (ap)
import Control.Monad.Morph (lift)
import Data.Functor.Classes (Eq1)
import Data.Deriving (deriveEq1)
import Text.PrettyPrint.ANSI.Leijen

pparens :: Bool -> Doc -> Doc
pparens True = parens
pparens False = id

data Kind = KType
  deriving (Eq)

prettyKind :: Kind -> Doc
prettyKind KType = text "Type"

data Constructor a
  = CBool
  | CVar a
  | CLambda Kind (Scope () Constructor a)
  | CApp (Constructor a) (Constructor a)
  deriving (Functor)

deriveEq1 ''Constructor

instance Applicative Constructor where
  pure = return
  (<*>) = ap

instance Monad Constructor where
  return = CVar

  CBool >>= _ = CBool
  CVar a >>= f = f a
  CLambda k b >>= f = CLambda k (b >>>= f)
  CApp a b >>= f = CApp (a >>= f) (b >>= f)

clam :: Eq a => a -> Kind -> Constructor a -> Constructor a
clam a k b = CLambda k (abstract1 a b)

prettyConstructor :: [String] -> Bool -> Constructor String -> Doc
prettyConstructor [] _ _ = error "ran out of type variables during constructor pretty printing"
prettyConstructor _ _ CBool = text "Bool*"
prettyConstructor _ _ (CVar a) = text a
prettyConstructor (av:avs) p (CLambda k body) = pparens p $
  char 'λ' <> text av <> char ':' <> prettyKind k <> char '.' <> prettyConstructor avs False (instantiate1 (CVar av) body)
prettyConstructor avs p (CApp a b) = pparens p $
  prettyConstructor avs True a <+> prettyConstructor avs True b

data Type c a
  = TBool
  | TT (c a)
  -- the body is a type with an additional bound constructor variable
  | TForall Kind (Type (Scope () c) a)
  deriving (Functor)

deriveEq1 ''Type

tforall :: Eq a => a -> Kind -> Type Constructor a -> Type Constructor a
tforall a k body = TForall k (tAbstract1 a body)

tAbstract1 :: Functor constructor => Eq a => a -> Type constructor a -> Type (Scope () constructor) a
tAbstract1 = go abstract1
  where
    go :: forall c c' a. Eq a
       => (forall v. Eq v => v -> c v -> c' v)
      -> a -> Type c a -> Type c' a
    go f a TBool = TBool
    go f a (TT c) = TT (f a c)
    go f a (TForall k b) = TForall k (go f' a b)
      where
        f' v = Scope . f (F v) . unscope

test :: Type Constructor String
test = tforall "foo" KType (TT (CApp (clam "x" KType (CVar "x")) (CVar "foo")))

prettyType :: [String] -> Bool -> Type Constructor String -> Doc
prettyType [] _ _ = error "ran out of type variables during type pretty printing"
prettyType _ _ TBool = text "Bool"
prettyType avs _ (TT c) = char 'T' <> parens (prettyConstructor avs False c)
prettyType (av:avs) p (TForall k body) = pparens p $
  char '∀' <> text av <> char ':' <> prettyKind k <> char '.' <> prettyType avs p (tInstantiate1 (CVar av) body)

tInstantiate1 :: forall operand b a.
  (Applicative operand, Monad operand) =>
  operand a -> Type (Scope b operand) a -> Type operand a
tInstantiate1 = go instantiate1
  where
    go :: forall o o' u. (forall v. operand v -> o v -> o' v) -> operand u -> Type o u -> Type o' u
    go f a TBool = TBool
    go f a (TT c) = TT (f a c)
    go f a (TForall k b) = TForall k (go f' a b)
      where
        f' v = Scope . f (fmap F v) . unscope

data Expr c a x
  = ETrue
  | EVar x
  | ELam (Type c a) (Scope () (Expr c a) x)
  -- TForall Kind (Type (Scope () c) a)
  | ETLam Kind (Expr (Scope () c) a x)
  deriving (Functor)

instance (Eq a, Monad c) => Applicative (Expr c a) where
  pure = return
  (<*>) = ap

instance (Eq a, Monad c) => Monad (Expr c a) where
  return = EVar

  ETrue >>= _ = ETrue
  EVar x >>= f = f x
  ELam t b >>= f = ELam t (b >>>= f)
  ETLam k b >>= f = ETLam k (b >>= liftCE . f)
  -- ETApp e t >>= f = ETApp (e >>= f) t

liftCE :: Monad c => Expr c a b -> Expr (Scope () c) a b
liftCE ETrue = ETrue
liftCE (EVar x) = EVar x
liftCE (ELam t b) = ELam (liftCT t) (hoistScope liftCE b)
liftCE (ETLam k b) = ETLam k (liftCE b)

liftCT :: Monad c => Type c a -> Type (Scope () c) a
liftCT TBool = TBool
liftCT (TT c) = TT (lift c)
liftCT (TForall k c) = TForall k (liftCT c)

elam :: Eq x => x -> Type c a -> Expr c a x -> Expr c a x
elam x t b = ELam t (abstract1 x b)

idA :: Expr Constructor String String
idA = elam "ex" (TT (CVar "a")) (EVar "ex")

-- instantiate a constructor in an expression
eInstantiateC1 :: Eq a => Monad c => c a -> Expr (Scope () c) a x -> Expr c a x
eInstantiateC1 a ETrue = ETrue
eInstantiateC1 a (EVar x) = EVar x
eInstantiateC1 a (ELam t b) = ELam (tInstantiate1 a t) (hoistScope (eInstantiateC1 a) b)
eInstantiateC1 a (ETLam k b) = ETLam k (eInstantiateC1 (lift a) b)

-- abstract over a constructor in an expression
eAbstractC1 :: Eq a => Functor c => a -> Expr c a x -> Expr (Scope () c) a x
eAbstractC1 a ETrue = ETrue
eAbstractC1 a (EVar x) = EVar x
eAbstractC1 a (ELam t b) = ELam (tAbstract1 a t) (hoistScope (eAbstractC1 a) b)
eAbstractC1 a (ETLam k b) = ETLam k (eAbstractC1 a b)

etlam :: Eq a => Monad c => a -> Kind -> Expr c a x -> Expr c a x
etlam a k b = ETLam k (eAbstractC1 a b) -- this should be actual abstract, not my misnamed one, I think

polyId :: Expr Constructor String String
polyId = etlam "a" KType (elam "ex" (TT (CVar "a")) (EVar "ex"))

prettyExpr :: ([String], [String]) -> Bool -> Expr Constructor String String -> Doc
prettyExpr ([], _) _ _ = error "ran out of variable names"
prettyExpr (_, []) _ _ = error "ran out of type variable names"
prettyExpr _ _ ETrue = text "true"
prettyExpr _ _ (EVar x) = text x
prettyExpr (v:vs, tvs) p (ELam t b) = pparens p $
  char 'λ' <> text v <> char ':' <> prettyType tvs False t <> char '.' <//> prettyExpr (vs, tvs) False (instantiate1 (EVar v) b)
prettyExpr (vs, tv:tvs) p (ETLam k b) = pparens p $
  char 'Λ' <> text tv <> char ':' <> prettyKind k <> char '.' <//> prettyExpr (vs, tvs) False (eInstantiateC1 (CVar tv) b)

{-

-- deriveShow1 ''Type
-- instance Show a => Show (Type a) where showsPrec = showsPrec1

-- tinstantiate1 :: Constructor a -> Scope () Type a -> Type a
-- tinstantiate1 d body = case unscope body of
--   TBool -> TBool
--   TT c -> TT _h
--   TForall k body -> _b

-- Is this a Bifunctor?
data Expr t x
  = ETrue
  | EVar x
  | ELam t (Scope () (Expr t) x)
  | ETLam Kind (Scope () (Expr t) x)
  | ETApp (Expr t x) t
  deriving (Functor)

deriveEq1 ''Expr

instance Applicative (Expr t) where
  pure = return
  (<*>) = ap

instance Monad (Expr t) where
  return = EVar

  ETrue >>= _ = ETrue
  EVar x >>= f = f x
  ELam t b >>= f = ELam t (b >>>= f)
  ETLam k b >>= f = ETLam k (b >>>= f)
  ETApp e t >>= f = ETApp (e >>= f) t

elam :: Eq x => x -> Type a -> Expr (Type a) x -> Expr (Type a) x
elam x t b = ELam t (abstract1 x b)

elam' :: String -> Type String -> Expr (Type String) String -> Expr (Type String) String
elam' = elam

prettyExpr :: ([String], [String]) -> Bool -> Expr (Type String) String -> Doc
prettyExpr _ _ ETrue = text "true"
prettyExpr _ _ (EVar x) = text x
prettyExpr (v:vs, tvs) p (ELam t b) = pparens p $ char '\\' <> text v <> char ':' <> prettyType tvs False t <> char '.' <//> prettyExpr (vs, tvs) False (instantiate1 (EVar v) b)



pe :: Expr (Type String) String -> Doc
pe = prettyExpr (["x", "y", "z"] <> [ "x" <> show x | x <- [0..] ], ["a", "b", "c"] <> [ "a" <> show x | x <- [0..] ]) False

-- bitraverse?
-- freeVariables :: Expr (Type String) String -> [String]
-- freeVariables = bitraverse
-}
tvars = ["α", "β", "γ"] <> [ "α" <> show x | x <- [0..] ]
evars = ["x", "y", "z"] <> [ "x" <> show x | x <- [0..] ]

someFunc :: IO ()
someFunc = do
  putDoc $ prettyConstructor tvars False (CApp (clam "x" KType (CVar "x")) (clam "y" KType CBool))
  putStrLn ""
  putDoc $ prettyType tvars False test
  putStrLn ""
  putDoc $ prettyExpr (evars, tvars) False idA
  putStrLn ""
  putDoc $ prettyExpr (evars, tvars) False polyId
  putStrLn ""
  -- putDoc $ pe $ elam' "a" TBool (elam' "c" TBool (EVar "c"))
  -- putStrLn ""
