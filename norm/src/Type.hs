module Type where

import GHC.Exts (sortWith)

type Label = String

type Var = Integer

data Type
  = Bool
  | Int
  | String
  | Rec Type
  | Nil
  | Cons (Label, Type) Type
  | List Type
  | Arrow Type Type
  deriving (Show)

rowToList :: Type -> [(Label, Type)]
rowToList row = sortWith fst (go row)
  where
    go Nil = []
    go (Cons p r) = p : go r
    go _ = error "Not a row"

closedRec :: [(Label, Type)] -> Type
closedRec = Rec . foldr Cons Nil
