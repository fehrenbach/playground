import Data.Vect

mutual
  data Ty = TyInt | TyString | TyList Nat Ty

total
interpTy : Ty -> Type
interpTy TyInt = Int
interpTy TyString = String
interpTy (TyList nst x) = List (Vect nst Nat, interpTy x)

using (G: Vect en Ty)
  data HasType : (i : Fin en) -> Vect en Ty -> Ty -> Type where
    Stop : HasType FZ (t :: G) t
    Pop : HasType k G t -> HasType (FS k) (u :: G) t

  data ATrace : Ty -> Type where
    -- Probably need an environment too
    TVal : (interpTy ty) -> ATrace ty
    TCup : ATrace (TyList n ty) -> (s : Nat) -> {auto sprf : plus n s = maximum n m}
        -> ATrace (TyList m ty) -> (t : Nat) -> {auto tprf : plus m t = maximum n m}
        -> ATrace (TyList (S (maximum n m)) ty)
    -- TFor : ATrace (TyList nst a) -> interpTy (TyList nst a) -> List (Vect mst Nat, ATrace (TyList mst b)) -> ATrace (TyList mst b)
    TSingleton : ATrace ty -> interpTy ty -> ATrace (TyList nst ty)

  data Expr : Vect en Ty -> Ty -> Type where
    Val : interpTy t -> Expr G t
    Var : HasType i G t -> Expr G t
    Cup : {n : Nat} -> {m : Nat}
       -> Expr G (TyList n a) -> {s : Nat} -> {auto sprf : plus n s = maximum n m}
       -> Expr G (TyList m a) -> {t : Nat} -> {auto tprf : plus m t = maximum n m}
       -> Expr G (TyList (S (maximum n m)) a)
    For : Expr (a :: G) (TyList m b) -> Expr G (TyList n a) -> Expr G (TyList (plus n m) b)
    Singleton : Expr G t -> Expr G (TyList 0 t)

  data Env : Vect n Ty -> Type where
    Nil  : Env Nil
    (::) : interpTy a -> Env G -> Env (a :: G)

  total
  lookup : HasType i G t -> Env G -> interpTy t
  lookup Stop (x :: y) = x
  lookup (Pop x) (y :: z) = lookup x z

  total
  consLabel : Vect n Nat -> List ((Vect m Nat), t) -> List (Vect (plus n m) Nat, t)
  consLabel l [] = []
  consLabel l ((ls, v) :: rest) = ((l ++ ls), v) :: consLabel l rest

  total
  extend : {n, k, m : Nat} -> t -> Vect n t -> plus n k = m -> Vect m t
  extend {n = Z}   {k = Z}   {m = Z  } _ _  Refl = []
  extend {n = Z}   {k = Z}   {m = S _} _ _  Refl impossible
  extend {n = Z}   {k = S _} {m = Z}   _ _  Refl impossible
  extend {n = Z}   {k = S j} {m = S j} y xs Refl = y :: extend y xs Refl
  extend {n = S _} {k = Z}   {m = Z} _ _ Refl impossible
  extend {n = S _} {k = S _} {m = Z} _ _ Refl impossible
  extend {n = S j} {k = Z}   {m = S (plus j Z)}     y (x :: xs) Refl = x :: extend y xs Refl
  extend {n = S j} {k = S k} {m = S (plus j (S k))} y (x :: xs) Refl = x :: extend y xs Refl

  total
  eval : Env G -> Expr G t -> interpTy t
  eval env (Val v) = v
  eval env (Var x) = lookup x env
  eval env (Cup {a} {n} {m} x {s} {sprf} y {t} {tprf}) =
       consLabel [1] (map (\(l, x) => (extend 0 l sprf, x)) (eval env x))
    ++ consLabel [2] (map (\(l, y) => (extend 0 l tprf, y)) (eval env y))
  eval env (For body input) = 
    concatMap (\(ln, vi) => consLabel ln (eval (vi :: env) body)) (eval env input)
  -- eval env (For body input) = ?evalFor
    -- concatMap (\x => eval (x :: env) body) (eval env input)
  eval env (Singleton x) = [ ([], eval env x) ]

  one : Expr G TyInt
  one = Val 1

  two : Expr G TyInt
  two = Val 2
  
  l1 : Expr G (TyList 0 TyInt)
  l1 = Singleton one
  
  l11 : Expr G (TyList 1 TyInt)
  l11 = Cup l1 l1
  
  l12 : Expr G (TyList 1 TyInt)
  l12 = Cup l1 (Singleton two)
  
  l112 : Expr G (TyList 2 TyInt)
  l112 = Cup l11 (Singleton two)

  l111 : Expr G (TyList 2 TyInt)
  l111 = For (Singleton one) l112

  ll111 : Expr G (TyList 2 (TyList 0 TyInt))
  ll111 = For (Singleton (Singleton one)) l112
  
  l123 : Expr G (TyList 2 TyInt)
  l123 = Cup l12 (Singleton (Val 3))

  l1122 : Expr G (TyList 2 TyInt)
  l1122 = For (Cup (Singleton (Var Stop)) (Singleton (Var Stop))) l12
