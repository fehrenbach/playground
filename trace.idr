import Data.Vect
import Data.Fin
import Record
-- import Data.HVect

total
mapIndexed : (a -> Nat -> b) -> List a -> List b
mapIndexed f l = go l Z
  where go [] i = []
        go (x :: xs) i = f x i :: go xs (S i)

total fst3 : (a, b, c) -> a
fst3 = fst

total snd3 : (a, b, c) -> b
snd3 = fst . snd

total thd3 : (a, b, c) -> c
thd3 = snd . snd

data ATrace = TVar | TVal t | TLam | TApp ATrace ATrace | TOp ATrace ATrace | TIf Bool ATrace ATrace
            | TCup ATrace ATrace | TFor ATrace (List (Nat, ATrace)) | TSingleton ATrace | TTrace
            | TTable String | TRecordNil | TRecordExt String ATrace ATrace

-- If we need to have the Type in there for records anyways, what do we get out of this?
-- I guess we constrain the set of types, no dependent pairs or other weird stuff.
-- Should we just use Idris types everywhere?
data Ty = TyInt | TyBool | TyList Ty | TyFun Ty Ty | TyTraced Ty
        -- | TyRecord (List (String, Ty))
        | TyRecord (List (String, Type))

total
interpTy : Ty -> Type
interpTy TyInt = Int
interpTy TyBool = Bool
interpTy (TyList x) = List (interpTy x)
interpTy (TyFun A T) = interpTy A -> interpTy T
interpTy (TyTraced t) = (interpTy t, ATrace)
-- confuses the totality checker
-- Is this something that recursion schemes would help with?
-- We just apply interpTy recursively on every Ty on a finite (and we know this, right?) tree structure
-- interpTy (TyRecord row) = Record {labelType=String} (map (\(l, t) => (l, interpTy t)) row)
interpTy (TyRecord row) = Record {labelType=String} row

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
    For : Expr (a :: G) (TyList b) -> Expr G (TyList a) -> Expr G (TyList b)
    Singleton : Expr G t -> Expr G (TyList t)
    Trace : Expr G t -> Expr G (TyTraced t)
    Data : Expr G (TyTraced t) -> Expr G t
    -- how to enforce record of flat base types?
    Table : String -> List (interpTy t) -> Expr G (TyList t)
    -- This seems to work, but it's annoying.
    RecordNil : Expr G (TyRecord [])
    RecordExt : (l : String) -> Expr G t -> Expr G (TyRecord row) -> Expr G (TyRecord ((l, interpTy t) :: row))

  data Env : Vect n Ty -> Type where
    Nil  : Env Nil
    (::) : interpTy a -> Env G -> Env (a :: G)

  total
  lookup : HasType i G t -> Env G -> interpTy t
  lookup Stop (x :: y) = x
  lookup (Pop x) (y :: z) = lookup x z

  total
  teval : Env G -> Expr G t -> (interpTy t, ATrace)
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
  teval env (For body input) =
    let
      (vinput, tinput) = teval env input
      res = mapIndexed (\x => \i => (i, teval (x :: env) body)) vinput
      v = concatMap snd3 res
      t = TFor tinput (map (\p => (fst3 p, thd3 p)) res)
    in (v, t)
  teval env (Singleton x) =
    let (vx, tx) = teval env x
    in ([ vx ], TSingleton tx)
  -- TTrace is a bit useless, maybe even harmful? We don't really need or want nested `traced` blocks.
  -- Options: - add more type state to Expr, to track whether we are inside a trace block already.
  --          - can we change interpTy (TyTrace t) to avoid nesting?
  teval env (Trace e) = (teval env e, TTrace)
  teval env (Data e) = fst (teval env e)
  teval env (Table n d) = (d, TTable n)
  teval env RecordNil = ([], TRecordNil)
  teval env (RecordExt l e rec) =
    let (ve, te) = teval env e
        (vr, tr) = teval env rec
    in ((l := ve) :: vr, TRecordExt l te tr)    

  total
  eval : Env G -> Expr G t -> interpTy t
  eval env (Var x) = lookup x env
  eval env (Val v) = v
  eval env (Lam body) = \x => eval (x :: env) body
  eval env (App f e) = eval env f (eval env e)
  eval env (Op op x y) = op (eval env x) (eval env y)
  eval env (If x y z) = if eval env x then eval env y else eval env z
  eval env (Cup x y) = eval env x ++ eval env y
  eval env (For body input) =
    concatMap (\x => eval (x :: env) body) (eval env input)
  eval env (Singleton x) = [ eval env x ]
  eval env (Trace e) = teval env e
  eval env (Data e) = fst (eval env e)
  eval env (Table _ d) = d
  eval env RecordNil = []
  eval env (RecordExt l e rec) = (l := eval env e) :: eval env rec

  one : Expr G TyInt
  one = Val 1

  incr : Expr G (TyFun TyInt TyInt)
  incr = Lam (Op (+) (Var Stop) one)

  l12345 : Expr G (TyList TyInt)
  l12345 = Val [ 1, 2, 3, 4, 5 ]

  l23456 : Expr G (TyList TyInt)
  l23456 = Op map incr l12345

  l34567 : Expr G (TyList TyInt)
  l34567 = For (Singleton (Op (+) (Var Stop) one)) l23456

  l357 : Expr G (TyList TyInt)
  l357 = For (If (Op (\x => \y => mod x 2 == y) (Var Stop) one) (Singleton (Var Stop)) (Val [])) l34567

  multl12l23 : Expr G (TyList TyInt)
  multl12l23 = For (For (Singleton (Op (*) (Var Stop) (Var (Pop Stop)))) l23456) l12345

  traceMult : Expr G (TyTraced (TyList TyInt))
  traceMult = Trace multl12l23

  -- should be equal to multl12l23
  dataTraceMult : Expr G (TyList TyInt)
  dataTraceMult = Data traceMult

  a2 : Expr G (TyRecord [("a", Int)])
  a2 = RecordExt "a" (Op (+) one one) RecordNil

  true : Expr G TyBool
  true = Val True

  a2bTrue : Expr G (TyRecord [("b", Bool), ("a", Int)])
  a2bTrue = RecordExt "b" true a2
  
  -- Okay, so this is difficult because of functional extensionality problems.
  -- total teval_consistent : (env : Env G) -> (e : Expr G t) -> eval env e = fst (teval env e)
