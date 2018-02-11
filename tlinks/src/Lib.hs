{-# LANGUAGE FlexibleContexts, DeriveFunctor, StandaloneDeriving, TemplateHaskell #-}
module Lib
    ( someFunc
    ) where

import Bound ((>>>=))
import Bound.Scope
import Control.Monad (ap)
import Data.Functor.Classes (Eq1)
import Data.Deriving (deriveEq1)
import Text.PrettyPrint.ANSI.Leijen

data Kind = KType
  deriving (Eq)

data Type a
  = TBool
  | TVar a
  | TForall Kind (Scope () Type a)
  deriving (Functor)

deriveEq1 ''Type
-- deriveShow1 ''Type
-- instance Show a => Show (Type a) where showsPrec = showsPrec1

instance Applicative Type where
  pure = return
  (<*>) = ap

instance Monad Type where
  return = TVar

  TBool >>= _ = TBool
  TVar x >>= f = f x
  TForall k b >>= f = TForall k (b >>>= f)

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

prettyType :: [String] -> Bool -> Type String -> Doc
prettyType _ _ TBool = text "Bool"

prettyExpr :: ([String], [String]) -> Bool -> Expr (Type String) String -> Doc
prettyExpr _ _ ETrue = text "true"
prettyExpr _ _ (EVar x) = text x
prettyExpr (v:vs, tvs) p (ELam t b) = pparens p $ char '\\' <> text v <> char ':' <> prettyType tvs False t <> char '.' <//> prettyExpr (vs, tvs) False (instantiate1 (EVar v) b)

pparens :: Bool -> Doc -> Doc
pparens True = parens
pparens False = id

pe :: Expr (Type String) String -> Doc
pe = prettyExpr (["x", "y", "z"] <> [ "x" <> show x | x <- [0..] ], ["a", "b", "c"] <> [ "a" <> show x | x <- [0..] ]) False

-- bitraverse?
-- freeVariables :: Expr (Type String) String -> [String]
-- freeVariables = bitraverse

someFunc :: IO ()
someFunc = putDoc $ pe $ elam' "a" TBool (elam' "c" TBool (EVar "c"))
