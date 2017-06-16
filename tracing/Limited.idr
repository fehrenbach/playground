module Limited

import Data.Fin
import Data.Vect

%access public export
%default total

infix 5 :->

data Kind : Type where
  Star : Kind
  Arrow : Kind -> Kind -> Kind
  
interpKi : Kind -> Type
interpKi Star = Type
interpKi (Arrow a b) = interpKi a -> interpKi b


using (K: Vect em Kind)
  namespace Ty
    data HasKind : (i : Fin em) -> Vect em Kind -> Kind -> Type where
      Stop : HasKind FZ (k :: K) k
      Pop  : HasKind j K k -> HasKind (FS j) (_ :: K) k
  
    data Ty : Vect em Kind -> Kind -> Type where
      Unit   : Ty K Star
      Num    : Ty K Star
      Var    : HasKind i K k -> Ty K k
      (+)    : Ty K Star -> Ty K Star -> Ty K Star
      (*)    : Ty K Star -> Ty K Star -> Ty K Star
      (:->)  : Ty K Star -> Ty K Star -> Ty K Star
      Forall : Ty (a :: K) k -> Ty K (Arrow a k)
      Mu     : Ty (k :: K) k -> Ty K k -- ?huh I HAVE NO CLUE

    PolyIdTy : Ty K (Arrow Star Star)
    PolyIdTy = Forall (Var Stop :-> Var Stop)

    data Env : Vect em Kind -> Type where
      Nil  : Env Nil
      (::) : interpKi a -> Env K -> Env (a :: K)
  
    lookup : Env K -> HasKind i K k -> interpKi k
    lookup (x :: y) Stop = x
    lookup (x :: z) (Pop y) = lookup z y

    interpTy : Env K -> Ty K k -> interpKi k
    interpTy _ Unit = ()
    interpTy _ Num = Int
    interpTy env (Var x) = lookup env x
    interpTy env (x + y) = Either (interpTy env x) (interpTy env y)
    interpTy env (x * y) = (interpTy env x, interpTy env y)
    interpTy env (x :-> y) = interpTy env x -> interpTy env y
    interpTy env (Forall x) = \alpha => interpTy (alpha :: env) x
    interpTy env (Mu x) =  ?uhWhatsTheRepresentationOfMu

    -- Unit : Ty K (Arrow Star Star)
    -- Unit = PolyIdTy
    
    IntListTy : Ty K Star
    IntListTy = Mu (Unit + (Num * (Var Stop)))

  using (G: Vect en (sk ** Ty K sk))
    namespace Expr
      data HasType : (i : Fin en) -> Vect em Kind -> Vect en (sk ** Ty K sk) -> Ty K k -> Type where
        Stop : HasType FZ K ((_ ** t) :: _) t
        Pop  : HasType j K G t -> HasType (FS j) K (_ :: G) t
    
      data Expr : Vect em Kind -> Vect en (sk ** Ty K sk) -> Ty K k -> Type where
      -- can't get the more general interpTy tenv t -> Expr .. t to work..
        Unit : Expr {k=Star} K G Unit
        Val  : Int -> Expr {k=Star} K G Num 
        Var  : HasType i K G t -> Expr K G t
        Pair : Expr K G a -> Expr K G b -> Expr K G (a * b)
        Fst  : Expr K G (a * b) -> Expr K G a
        Snd  : Expr K G (a * b) -> Expr K G b
        Inl  : Expr K G a -> Expr K G (a + b)
        Inr  : Expr K G b -> Expr K G (a + b)
        Case : Expr K G (a + b) -> Lazy (Expr K ((_ ** a) :: G) c) -> Lazy (Expr K ((_ ** b) :: G) c) -> Expr K G c
        -- Wrap : Expr K G b -> Expr G (Mu a)
        -- Unwrap : Expr K G (Mu a) -> Expr K G b

    one : Expr K G Num
    one = Val 1

    oneone : Expr K G (Num * Num)
    oneone = Pair (Val 1) (Val 1)
    
    -- nil : Expr K G IntListTy
    -- nil = Wrap (Inl {b=Num * Var Stop} Unit)

    -- incr : Expr K G (Num :-> Num)
    -- incr = Val (\x => x + 1)
    
    

{-
    namespace Expr
      data HasType : (i : Fin en) -> Vect en (Ty s) -> Ty s -> Type where
        Stop : HasType FZ (t :: G) t
        Pop  : HasType j G t -> HasType (FS j) (u :: G) t
  
      data Expr : Vect em Type -> Vect en (Ty em) -> Ty em -> Type where
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
        TAbs : Expr T G e -> Expr G (Forall e)
        TApp : Expr T [] (Forall e) -> (a : Ty _) -> Expr ((interpTy T a) :: T) [] e
        Roll : Expr (a :: T) [] e -> Expr T [] (Mu e)
        -- Roll : Expr {em = S k} (a :: T) G t -> Expr T G (Mu t)
        -- roll : t[mu a . t / a] -> mu a. t
        -- unroll : mu a . t -> t[mu a . t / a]

    one : Expr T G Num
    one = Val 1

    incr : Expr T G (Num :-> Num)
    incr = Val (\x => x + 1)
    
    two : Expr T G Num
    two = App incr one

    metaId : Expr T G PolyIdTy
    metaId = Val (\ty => \x => x)
    
    objId : Expr [] [] PolyIdTy
    objId = TAbs (Lam (Var Stop))

    monoId : Expr T G (Num :-> Num)
    monoId = Lam (Var Stop)
    
    -- oneTwo : Expr T G IntListTy
    -- oneTwo = (Inl metaId)

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

unit : Expr t g OneTy
unit = metaId


nil : Expr [] [] IntListTy
nil = Roll {a=interpTy [] (Mu (Forall (Var FZ :-> Var FZ) + Num * Var FZ))} (Inl {b=Num * Var FZ} unit)

-- singletonOne : Expr [] [] IntListTy
-- singletonOne = Roll {a=interpTy [] (Mu (Forall (Var FZ :-> Var FZ) + Num * Var FZ))} (Inr (Pair one nil))

-}
