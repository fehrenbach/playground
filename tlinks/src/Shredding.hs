module Shredding where

import Common
import Type (Type)
import qualified Type as T
import Expr (Expr)
import qualified Expr as E

import Data.Bifunctor (second)

data Path
  = Empty
  | Down Path
  | Select Label Path
  deriving (Eq, Ord, Show)

paths :: Type a -> [Path]
paths o | T.isBaseType o = []
paths (T.Record row) = [ Select l p | (l, a) <- T.rowToList row, p <- paths a ]
paths (T.List a) = Empty : [ Down p | p <- paths a ]

innerShredding :: Type a -> Type a
innerShredding o | T.isBaseType o = o
innerShredding (T.Record row) = T.record (map (second innerShredding) (T.rowToList row))
innerShredding (T.List _) = T.Index

outerShredding :: Path -> Type a -> Type a
outerShredding Empty (T.List a) = T.List (T.record [("1", T.Index)
                                                   ,("2", innerShredding a)])
outerShredding (Down p) (T.List a) = outerShredding p a
outerShredding (Select l p) (T.Record row) = case lookup l (T.rowToList row) of
  Just a -> outerShredding p a
