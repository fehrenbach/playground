import Data.Vect
import Data.Fin

data Ty = TInt | TBool | TList Ty

total
interpTy : Ty -> Type
interpTy TInt = Int
interpTy TBool = Bool
interpTy (TList x) = List (interpTy x)

data Expr : Ty -> Type where
  EInt : Int -> Expr TInt -- EConst 5 complains about something with interpTy t not being a number, or something
  EConst : interpTy t -> Expr t
  EVar : interpTy t -> Expr t
  ESingleton : Expr t -> Expr (TList t)
  EUnion : Expr (TList t) -> Expr (TList t) -> Expr (TList t)
  EFor : (Expr a -> Expr (TList b)) -> Expr (TList a) -> Expr (TList b)

-- total
eval : Expr t -> interpTy t
eval (EInt i) = i
eval (EConst x) = x
eval (EVar v) = v
eval (ESingleton x) = [ eval x ]
eval (EUnion x y) =
  let l1 = eval x
      l2 = eval y
  in l1 ++ l2
eval (EFor f l) =
  concatMap (\x => eval (f (EVar x))) (eval l)

l123 : List Int
l123 = eval (EUnion (ESingleton (EInt 1)) (EConst [2, 3]))

l222 : List Int
l222 = eval (EFor (\x => ESingleton (EInt 2)) (EUnion (ESingleton (EInt 1)) (EConst [2, 3])))

-- data Trace : Ty -> Type where
--   TVar : Trace t -> Trace t
--   TConst : (interpTy t) -> Trace t
--   TSingleton : Trace t -> Trace (TList t)
--   TUnion : Trace (TList t) -> Trace (TList t) -> Trace (TList t)
--   TFor : Trace (TList s) -> List (Trace t) -> Trace (TList t)

-- teval : Expr t -> Trace t
-- teval (EVar v) = TVar (TConst v) -- Ugh, this doesn't make any sense
-- teval (EInt x) = TConst x
-- teval (EConst x) = TConst x
-- teval (ESingleton x) = TSingleton (teval x)
-- teval (EUnion x y) = TUnion (teval x) (teval y)
-- teval (EFor f l) = ?a (teval l)

-- untrace : Trace t -> (interpTy t)
-- untrace (TConst x) = x
-- untrace (TSingleton x) = [ untrace x ]
-- untrace (TUnion x y) = untrace x ++ untrace y

-- untracelist : Trace (TList t) -> List (Trace t)
-- untracelist (TVar l) = ?untracelist_rhs_1
-- untracelist (TConst x) = ?untracelist_rhs_2
-- untracelist (TSingleton x) = ?untracelist_rhs_3
-- untracelist (TUnion x y) = ?untracelist_rhs_4
-- untracelist (TFor x xs) = ?untracelist_rhs_5
