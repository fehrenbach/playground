{-# LANGUAGE GADTs  #-}

module Lib where

someFunc :: IO ()
someFunc = putStrLn "someFunc"

-- http://cedric.cnam.fr/~puechm/typeful.ml
-- (* NbE in CPS, call-by-value *)

-- module CPS_CBV = struct

--   type 'a k and 'a v and 'a y
data K a
data V a
data Y a

--   (* Intermediate language of values in CPS, typed *)

--   type 'a vl = VFun : ('a vl -> 'b md) -> ('a -> 'b) vl
--              | VBase : base -> base vl
--              | VBool : bool -> bool vl
--   and 'a md = ('a vl -> o) -> o
--   and 'a x = 'a vl

data Value a where
  VFun :: (Value a -> MD b) -> Value (a -> b)
  VBase :: Base -> Value Base
  VBool :: Bool -> Value Bool

type MD a = (Value a -> O) -> O

--   (* Typed target language: Î²-normal, Î·-long Î»-terms
--      (modulo commuting conversions) *)

--   and o = SIf : bool at * o * o -> o
--         | SRet : 'a k * 'a nf -> o
--         | SBind : ('a -> 'b) at * 'a nf * ('b v -> o) -> o

data O where
  SIf :: AT Bool -> O -> O -> O
  SRet :: K a -> NF a -> O
  SBind :: AT (a -> b) -> NF a -> (V b -> O) -> O

--   and 'a nf = NBool : bool -> bool nf
--             | NLam : ('a y -> 'b k -> o) -> ('a -> 'b) nf
--             | NAt : base at -> base nf

data NF a where
  NBool :: Bool -> NF Bool
  NLam :: (Y a -> K b -> O) -> NF (a -> b)
  NAt :: AT Base -> NF Base

--   and 'a at = AVar of 'a y
--             | AVal of 'a v

data AT a
  = AVar (Y a)
  | AVal (V a)

--   and base = Atom of base at

data Base = Atom (AT Base) -- what?

--   (* Two examples of values in CPS *)

--   let id : type a. (a -> a) vl = VFun (fun x k -> k x)

id :: Value (a -> a)
id = VFun (\x k -> k x)

--   let app : type a b. ((a -> b) -> a -> b) vl =
--     VFun (fun (VFun f) k -> k (VFun (fun x k -> f x (fun v -> k v))))

app :: Value ((a -> b) -> a -> b)
app = VFun (\(VFun f) k -> k (VFun (\x k -> f x (\v -> k v))))

--   (* Typed source language, with Booleans and call/cc *)

--   type 'a tm =
--     | If : bool tm * 'a tm * 'a tm -> 'a tm
--     | CC : (('a -> 'b) -> 'a) tm -> 'a tm
--     | Lam : ('a x -> 'b tm) -> ('a -> 'b) tm
--     | App : ('a -> 'b) tm * 'a tm -> 'b tm
--     | Var : 'a x -> 'a tm

data Term a where
  If :: Term Bool -> Term a -> Term a -> Term a
  CC :: Term ((a -> b) -> a) -> Term a
  Lam :: (Value a -> Term b) -> Term (a -> b)
  App :: Term (a -> b) -> Term a -> Term b
  Var :: Value a -> Term a

--   (* Example of a source term *)

--   let tt = Var (VBool true)
tt :: Term Bool
tt = Var (VBool True)

--   (* Evaluation function in CPS CBV: from source to intermediate *)

--   let rec eval : type a. a tm -> a md = function
--     | Var x -> fun c -> c x
--     | Lam f -> fun c -> c (VFun (fun x k -> eval (f x) k))
--     | App (m, n) -> fun c -> eval m (fun (VFun f) -> eval n (fun n -> f n c))
--     | If (b, m, n) -> fun c -> eval b (fun (VBool b) ->
--         if b then eval m c else eval n c)
--     | CC m -> fun c -> eval m (fun (VFun f) -> f (VFun (fun x _ -> c x)) c)

eval :: Term a -> MD a
eval (Var x) = \c -> c x
eval (Lam f) = \c -> c (VFun (\x k -> eval (f x) k))
eval (App m n) = \c -> eval m (\(VFun f) -> eval n (\n -> f n c))
eval (If b m n) = \c -> eval b (\(VBool b) -> if b then eval m c else eval n c)
eval (CC m) = \c -> eval m (\(VFun f) -> f (VFun (\x _ -> c x)) c)

--   let ex : type a. (a -> a) tm = Lam (fun x -> If (Var (VBool true), Var x, Var x))
ex :: Term (a -> a)
ex = Lam (\x -> If tt (Var x) (Var x))

--   (* Annotated simple types, enriched with Booleans *)

--   type 'a tp = Bool : bool tp
--              | Base : base tp
--              | Arr : 'a tp * 'b tp -> ('a -> 'b) tp
data Type a where
  Boolean :: Type Bool
  Base :: Type Base
  Arr :: Type a -> Type b -> Type (a -> b)

--   (* reify and reflect in CPS CBV: from intermediate to target *)

--   let rec reify : type a. a tp -> a vl -> (a nf -> o) -> o =
--     fun a v -> match a, v with
--       | Arr (a, b), VFun f -> fun c -> c (NLam (fun x k ->
--           reflect a (AVar x) (fun x -> f x (fun v ->
--               reify b v (fun v -> SRet (k, v))))))
--       | Base, VBase (Atom r) -> fun c -> c (NAt r)
--       | Bool, VBool b -> fun c -> c (NBool b)

reify :: Type a -> Value a -> (NF a -> O) -> O
reify (Arr a b) (VFun f) = \c -> c (NLam (\x k -> reflect a (AVar x) (\x -> f x (\v -> reify b v (\v -> SRet k v)))))
reify Base (VBase (Atom r)) = \c -> c (NAt r)
reify Boolean (VBool b) = \c -> c (NBool b)

--   and reflect : type a. a tp -> a at -> (a vl -> o) -> o =
--     fun a x -> match a, x with
--       | Arr (a, b), f -> fun c -> c (VFun (fun x k ->
--           reify a x (fun x -> SBind (f, x, fun v ->
--               reflect b (AVal v) (fun v -> k v)))))
--       | Base, r -> fun c -> c (VBase (Atom r))
--       | Bool, b -> fun c -> SIf (b, c (VBool true), c (VBool false))

reflect :: Type a -> AT a -> (Value a -> O) -> O
reflect (Arr a b) f = \c -> c (VFun (\x k -> reify a x (\x -> SBind f x (\v -> reflect b (AVal v) (\v -> k v)))))
reflect Base r = \c -> c (VBase (Atom r))
reflect Boolean b = \c -> SIf b (c (VBool True)) (c (VBool False))

--   (* The final NbE function *)

--   let nbe : type a. a tp -> a tm -> (a nf -> o) -> o =
--     fun a m k -> eval m (fun m -> reify a m k)

nbe :: Type a -> Term a -> (NF a -> O) -> O
nbe a m k = eval m (\m -> reify a m k)

--   type 'a c = Init of ('a k -> o)
data C a = Init (K a -> O)

--   let nbe : type a. a tp -> a tm -> a c = fun a m ->
--     Init (fun k -> eval m (fun m -> reify a m (fun v -> SRet (k, v))))
nbe' :: Type a -> Term a -> C a
nbe' a m = Init (\k -> eval m (\m -> reify a m (\v -> SRet k v)))

-- end
