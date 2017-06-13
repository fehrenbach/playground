module Limited

import Data.Fin
import Data.Vect

%access public export
%default total

infix 5 :->

namespace Ty
  data Ty : Nat -> Type where
    Num    : Ty s
    Var    : Fin s -> Ty s
    (+)    : Ty s -> Ty s -> Ty s
    (*)    : Ty s -> Ty s -> Ty s
    (:->)  : Ty s -> Ty s -> Ty s
    -- Kappa  : Ty s -> Ty (S s) -> Ty s
    Forall : Ty (S s) -> Ty s

  PolyIdTy : Ty n
  PolyIdTy = Forall (Var 0 :-> Var 0)

  interpTy : Vect s Type -> Ty s -> Type
  interpTy env Num = Int
  interpTy env (Var v) = index v env
  interpTy env (x + y) = Either (interpTy env x) (interpTy env y)
  interpTy env (x * y) = (interpTy env x, interpTy env y)
  interpTy env (x :-> y) = interpTy env x -> interpTy env y
-- interpTy env (Kappa x y) = 
  interpTy env (Forall x) = (alpha : Type) -> interpTy (alpha :: env) x

using (T : Vect em Type) 
  using (G: Vect en (Ty em))

    namespace Expr
      data HasType : (i : Fin en) -> Vect en (Ty s) -> Ty s -> Type where
        Stop : HasType FZ (t :: G) t
        Pop  : HasType j G t -> HasType (FS j) (u :: G) t
  
      data Expr : Vect em Type -> Vect en (Ty s) -> Ty s -> Type where
        Val  : interpTy T t -> Expr T G t
        Var  : HasType i G t -> Expr T G t
        Pair : Expr T G a -> Expr T G b -> Expr T G (a * b)
        Fst  : Expr T G (a * b) -> Expr T G a
        Snd  : Expr T G (a * b) -> Expr T G b
        Inl  : Expr T G a -> Expr T G (a + b)
        Inr  : Expr T G b -> Expr T G (a + b)
        Case : Expr T G (a + b) -> Lazy (Expr T (a :: G) c) -> Lazy (Expr T (b :: G) c) -> Expr T G c
        Lam  : Expr T (a :: G) b -> Expr T G (a :-> b)
        App  : Expr T G (a :-> b) -> Expr T G a -> Expr T G b

    one : Expr T G Num
    one = Val 1

    incr : Expr T G (Num :-> Num)
    incr = Val (\x => x + 1)

    metaId : Expr T G PolyIdTy
    metaId = Val (\ty => \x => x)

    monoId : Expr T G (Num :-> Num)
    monoId = Lam (Var Stop)

    namespace Env
      data Env : Vect em Type -> Vect en (Ty s) -> Type where
        Nil  : Env T Nil
        (::) : interpTy T a -> Env T G -> Env T (a :: G)
  
    lookup : Env T G -> HasType i G t -> interpTy T t
    lookup (x :: y) Stop = x
    lookup (x :: z) (Pop y) = lookup z y
  
    eval : Env T G -> Expr T G t -> interpTy T t
    eval env (Val x) = x
    eval env (Var v) = lookup env v
    eval env (Pair x y) = (eval env x, eval env y)
    eval env (Fst x) = fst (eval env x)
    eval env (Snd x) = snd (eval env x)
    eval env (Inl x) = Left (eval env x)
    eval env (Inr x) = Right (eval env x)
    eval env (Case x y z) = case eval env x of
      Left v => eval (v :: env) y
      Right v => eval (v :: env) z
    eval env (Lam e) = \x => eval (x :: env) e
    eval env (App x y) = (eval env x) (eval env y)

-- Evaluate a closed expression with less faff
go : Expr [] [] t -> interpTy [] t
go = eval []
