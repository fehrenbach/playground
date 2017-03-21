import Data.Vect
import Data.Fin

data Ty = TyInt | TyBool | TyList Ty | TyFun Ty Ty

total
interpTy : Ty -> Type
interpTy TyInt = Int
interpTy TyBool = Bool
interpTy (TyList x) = List (interpTy x)
interpTy (TyFun A T) = interpTy A -> interpTy T

using (G: Vect n Ty)

  data HasType : (i : Fin n) -> Vect n Ty -> Ty -> Type where
    Stop : HasType FZ (t :: G) t
    Pop : HasType k G t -> HasType (FS k) (u :: G) t

  data Expr : Vect n Ty -> Ty -> Type where
    Var : HasType i G t -> Expr G t
    Val : interpTy t -> Expr G t
    Lam : Expr (a :: G) t -> Expr G (TyFun a t)
    App : Expr G (TyFun a t) -> Expr G a -> Expr G t
    Op  : (interpTy a -> interpTy b -> interpTy c) -> Expr G a -> Expr G b -> Expr G c
    If  : Expr G TyBool -> Lazy (Expr G a) -> Lazy (Expr G a) -> Expr G a
    Cup : Expr G (TyList a) -> Expr G (TyList a) -> Expr G (TyList a)

  data Env : Vect n Ty -> Type where
    Nil  : Env Nil
    (::) : interpTy a -> Env G -> Env (a :: G)

  total
  lookup : HasType i G t -> Env G -> interpTy t
  lookup Stop (x :: y) = x
  lookup (Pop x) (y :: z) = lookup x z

  total
  eval : Env G -> Expr G t -> interpTy t
  eval env (Var x) = lookup x env
  eval env (Val v) = v
  eval env (Lam body) = \x => eval (x :: env) body
  eval env (App f e) = eval env f (eval env e)
  eval env (Op op x y) = op (eval env x) (eval env y)
  eval env (If x y z) = if eval env x then eval env y else eval env z
  eval env (Cup x y) = eval env x ++ eval env y

  data Trace = TVar | TVal t | TLam | TApp Trace Trace | TOp Trace Trace | TIf Bool Trace Trace | TCup Trace Trace

  total
  teval : Env G -> Expr G t -> (interpTy t, Trace)
  teval env (Var x) = (lookup x env, TVar)
  teval env (Val x) = (x, TVal x)
  teval env (Lam e) = (\x => fst (teval (x :: env) e), TLam)
  teval env (App f a) =
    let (vf, tf) = teval env f
        (va, ta) = teval env a
    in (vf va, TApp tf ta)
  teval env (Op f x y) =
    let (vx, tx) = teval env x
        (vy, ty) = teval env y
    in (f vx vy, TOp tx ty)
  teval env (If x y z) =
    let (vx, tx) = teval env x
    -- Idris thinks the nice version might not be total :(
        -- (ve, te) = teval env (if vx then y else z)
    -- in (ve, TIf vx tx te)
    in if vx then let (vy, ty) = teval env y in (vy, TIf vx tx ty)
             else let (vz, tz) = teval env z in (vz, TIf vx tx tz)
  teval env (Cup x y) =
    let (vx, tx) = teval env x
        (vy, ty) = teval env y
    in (vx ++ vy, TCup tx ty)

  one : Expr G TyInt
  one = Val 1

  incr : Expr G (TyFun TyInt TyInt)
  incr = Lam (Op (+) (Var Stop) one)
  
  l12345 : Expr G (TyList TyInt)
  l12345 = Val [ 1, 2, 3, 4, 5 ]

  l23456 : Expr G (TyList TyInt)
  l23456 = Op map incr l12345
