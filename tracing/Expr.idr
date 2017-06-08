module Expr

import Data.Vect
import Data.Fin
import Record
import TaggedUnion
import Ty

%access public export
%default total

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

total
consLabels : Vect n Nat -> List ((Vect m Nat), t) -> List (Vect (plus n m) Nat, t)
consLabels l [] = []
consLabels l ((ls, v) :: rest) = ((l ++ ls), v) :: consLabels l rest

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

mutual
  total
  interpTy : Ty -> Type
  interpTy TyInt = Int
  interpTy TyBool = Bool
  interpTy TyString = String
  interpTy (TyList n x) = List (Vect n Nat, interpTy x)
  interpTy (TyFun A T) = interpTy A -> interpTy T
  interpTy (TyRecord rty) = Record {labelType=String} (interpRTy rty)
  interpTy (TyVariant vty) = Variant (interpVTy vty)

  total
  interpRTy : RTy -> List (String, Type)
  interpRTy TyRecordNil = []
  interpRTy (TyRecordExt l ty rty) = (l, interpTy ty) :: interpRTy rty
  
  interpVTy : VTy -> List (String, Type)
  interpVTy TyVariantNil = []
  interpVTy (TyVariantExt x y z) = (x, interpTy y) :: interpVTy z

-- Convert a proof of label presence for object language records to a proof of label presence for idris records so we can use projection from there
objToMetaLabelPresenceProof : TyLabelPresent label row ty -> LabelPresent label (interpRTy row) (interpTy ty)
objToMetaLabelPresenceProof Here = Here
objToMetaLabelPresenceProof (There prf) = There (objToMetaLabelPresenceProof prf)

infix 5 :?

using (G: Vect en Ty)
  data HasType : (i : Fin en) -> Vect en Ty -> Ty -> Type where
    Stop : HasType FZ (t :: G) t
    Pop : HasType k G t -> HasType (FS k) (u :: G) t

  mutual 
    data Expr : Vect en Ty -> Ty -> Type where
      Var
         : HasType i G t
        -> Expr G t
      Val
         : interpTy t
        -> Expr G t
      Lam
         : Expr (a :: G) t
        -> Expr G (TyFun a t)
      App
         : Expr G (TyFun a t)
        -> Expr G a
        -> Expr G t
      (&&)
         : Expr G TyBool
        -> Expr G TyBool
        -> Expr G TyBool
      (==)
         : Eq (interpTy a)
        => Expr G a
        -> Expr G a
        -> Expr G TyBool
      Op1
         : (interpTy a -> interpTy b)
        -> Expr G a
        -> Expr G b
      Op2
         : (interpTy a -> interpTy b -> interpTy c)
        -> Expr G a
        -> Expr G b
        -> Expr G c
      If
         : Expr G TyBool
        -> Lazy (Expr G a)
        -> Lazy (Expr G a)
        -> Expr G a
      Cup
         : {n, m : Nat}
        -> Expr G (TyList n a) -> {s : Nat} -> { auto sprf : plus n s = maximum n m }
        -> Expr G (TyList m a) -> {t : Nat} -> { auto tprf : plus m t = maximum n m }
        -> Expr G (TyList (S (maximum n m)) a)
      For
         : Expr (a :: G) (TyList m b)
        -> Expr G (TyList n a)
        -> Expr G (TyList (plus n m) b)
      Singleton
         : Expr G t
        -> Expr G (TyList 0 t)
      Table
         : String
        -> List (interpTy (TyRecord row))
        -> { auto prf : IsBaseRow row }
        -> Expr G (TyList 1 (TyRecord row))
      RecordNil
         : Expr G (TyRecord TyRecordNil)
      RecordExt
         : (l : String)
        -> Expr G t
        -> Expr G (TyRecord row)
        -> Expr G (TyRecord (TyRecordExt l t row))
      Project
         : (l : String)
        -> Expr G (TyRecord row)
        -> { auto prf : TyLabelPresent l row ty }
        -> Expr G ty
      Constr
         : (l: String)
        -> Expr G a
        -> { auto prf : TyLabelPresent l a v }
        -> Expr G (TyVariant v)
      Match
         : Expr G (TyVariant v)
        -> Cases G v t
        -> Expr G t
      
    data Case' : Vect en Ty -> String -> (i: Ty) -> (o: Ty) -> Type where
      Case : {a, b: Ty} -> (label : String) -> Expr (a :: G) b -> Case' G label a b

    data Cases : Vect en Ty -> VTy -> Ty -> Type where
      Nil  : Cases G TyVariantNil t
      (::) : Case' G l r t -> Cases G v t -> Cases G (TyVariantExt l r v) t

      
  namespace Env
    data Env : Vect n Ty -> Type where
      Nil  : Env Nil
      (::) : interpTy a -> Env G -> Env (a :: G)

    total
    lookup : HasType i G t -> Env G -> interpTy t
    lookup Stop (x :: y) = x
    lookup (Pop x) (y :: z) = lookup x z

  total
  variantPresenceProof : TyLabelPresent l a v -> LabelPresent l (interpTy a) (interpVTy v)
  variantPresenceProof Here = Here
  variantPresenceProof (There z) = There (variantPresenceProof z)

  total
  eval : Env G -> Expr G t -> interpTy t
  eval env (Var x) = lookup x env
  eval env (Val v) = v
  eval env (Lam body) = \x => eval (x :: env) body
  eval env (App f e) = eval env f (eval env e)
  eval env ((&&) x y) = eval env x && eval env y
  eval env ((==) x y) = eval env x == eval env y
  eval env (Op1 f x) = f (eval env x)
  eval env (Op2 op x y) = op (eval env x) (eval env y)
  eval env (If x y z) = if eval env x then eval env y else eval env z
  eval env (Cup {a} {n} {m} x {s} {sprf} y {t} {tprf}) =
       consLabels [1] (map (\(l, x) => (extend 0 l sprf, x)) (eval env x))
    ++ consLabels [2] (map (\(l, y) => (extend 0 l tprf, y)) (eval env y))
  eval env (For body input) =
    concatMap (\(ln, vi) => consLabels ln (eval (vi :: env) body)) (eval env input)
  eval env (Singleton x) = [ ([], eval env x) ]
  eval env (Table _ d) = mapIndexed (\x => \i => ([i], x)) d
  eval env RecordNil = []
  eval env (RecordExt l e rec) = (l := eval env e) :: eval env rec
  eval env (Project l r { prf }) = project' l (eval env r) (objToMetaLabelPresenceProof prf)
  eval env (Constr l e {prf}) = InV l (eval env e) {prf=variantPresenceProof prf}
  eval env (Match e cs) =
    match env (eval env e) cs
   where
    match : Env G -> interpTy (TyVariant v) -> Cases G v t -> interpTy t
    match env (InV _ x {prf = Here}) ((Case _ e) :: _) = eval (x :: env) e
    match env (InV label x {prf = (There w)}) (y :: z) = match env (InV label x {prf=w}) z

  one : Expr G TyInt
  one = Val 1

  incr : Expr G (TyFun TyInt TyInt)
  incr = Lam (Op2 (+) (Var Stop) one)

  l12345 : Expr G (TyList 1 TyInt)
  l12345 = Val [ ([0], 1), ([1], 2), ([2], 3), ([3], 4), ([4], 5) ]

  l23456 : Expr G (TyList 1 TyInt)
  l23456 = For (Singleton (App incr (Var Stop))) l12345

  l34567 : Expr G (TyList 1 TyInt)
  l34567 = For (Singleton (Op2 (+) (Var Stop) one)) l23456
  
  OneOrPlusOne : Ty
  OneOrPlusOne = TyVariant (TyVariantExt "i" TyInt (TyVariantExt "f" (TyFun TyInt TyInt) TyVariantNil))
  
  varOne : Expr G OneOrPlusOne
  varOne = Constr "i" one
  
  varPlusOne : Expr G OneOrPlusOne
  varPlusOne = Constr "f" incr
  
  -- two : Expr G TyInt
  -- two = Match varPlusOne [ Case "i" (\i => Val 2)
                         -- , Case "f" (\f => App f (Val 1)) ]

  two : Expr G TyInt
  two = Match varPlusOne [ Case "i" (App incr (Var Stop)) 
                         , Case "f" (App (Var Stop) (Val 1)) ]

  two' : Expr G TyInt
  two' = Match varOne [ Case "i" (App incr (Var Stop)) 
                      , Case "f" (App (Var Stop) (Val 1)) ]


  partial -- mod is not total, or something
  l357 : Expr G (TyList 1 TyInt)
  l357 = For (If (Op2 (\x => \y => mod x 2 == y) (Var Stop) one) (Singleton (Var Stop)) (Val [])) l34567

  multl12l23 : Expr G (TyList 2 TyInt)
  multl12l23 = For (For (Singleton (Op2 (*) (Var Stop) (Var (Pop Stop)))) l23456) l12345

  -- traceMult : Expr G (TyTraced (TyList TyInt))
  -- traceMult = Trace multl12l23

  -- should be equal to multl12l23
  -- dataTraceMult : Expr G (TyList TyInt)
  -- dataTraceMult = Data traceMult

  a2 : Expr G (TyRecord (TyRecordExt "a" TyInt TyRecordNil))
  a2 = RecordExt "a" (Op2 (+) one one) RecordNil

  true : Expr G TyBool
  true = Val True

  a2bTrue : Expr G (TyRecord (TyRecordExt "b" TyBool (TyRecordExt "a" TyInt TyRecordNil)))
  a2bTrue = RecordExt "b" true a2

  a2bTruePa : Expr G TyInt
  a2bTruePa = Project "a" a2bTrue

  agencies : Expr G (TyList 1 (TyRecord (TyRecordExt "name" TyString (TyRecordExt "based_in" TyString (TyRecordExt "phone" TyString TyRecordNil)))))
  agencies = Table "agencies"
    [ [ "name" := "EdinTours", "based_in" := "Edinburgh", "phone" := "412 1200" ],
      [ "name" := "Burns's", "based_in" := "Glasgow", "phone" := "607 3000" ] ]

  eTours : Expr G (TyList 1 (TyRecord (TyRecordExt "name" TyString (TyRecordExt "destination" TyString (TyRecordExt "type" TyString (TyRecordExt "price" TyInt TyRecordNil))))))
  eTours = Table "externalTours"
    [ [ "name" := "EdinTours", "destination" := "Edinburgh", "type" := "bus", "price" := 20 ],
      [ "name" := "EdinTours", "destination" := "Loch Ness", "type" := "bus", "price" := 50 ],
      [ "name" := "EdinTours", "destination" := "och Ness", "type" := "boat", "price" := 200 ],
      [ "name" := "EdinTours", "destination" := "Firth of Forth", "type" := "boat", "price" := 50 ],
      [ "name" := "Burns's", "destination" := "Islay", "type" := "boat", "price" := 100 ],
      [ "name" := "Burns's", "destination" := "Mallaig", "type" := "train", "price" := 40 ] ]

  boatTours : Expr G (TyList 2 (TyRecord (TyRecordExt "name" TyString (TyRecordExt "phone" TyString TyRecordNil))))
  boatTours =
    For (For (If ((the (Expr _ TyString) (Project "name" (Var (Pop Stop)))) ==
                       (the (Expr _ TyString) (Project "name" (Var Stop)))
                  && ((the (Expr _ TyString) (Project "type" (Var Stop)))
                     == (the (Expr _ TyString) (Val "boat"))))
      (Singleton (RecordExt "name" (Project "name" (Var Stop)) (RecordExt "phone" (Project "phone" (Var (Pop Stop))) RecordNil)))
      (Val [])) eTours) agencies

  bigR : Expr G (TyList 1 (TyRecord (TyRecordExt "A" TyInt (TyRecordExt "B" TyInt (TyRecordExt "C" TyInt TyRecordNil)))))
  bigR = Table "R" [ [ "A" := 1, "B" := 2, "C" := 7 ]
                   , [ "A" := 2, "B" := 3, "C" := 8 ]
                   , [ "A" := 4, "B" := 3, "C" := 9 ] ]

  bigQ : Expr G (TyList 1 (TyRecord (TyRecordExt "A" TyInt (TyRecordExt "B" TyInt TyRecordNil))))
  bigQ = For (If (Op2 (the (Int -> Int -> Bool) (==))
                      (Project "B" (Var Stop)) (the (Expr _ TyInt) (Val 3)))
                 (Singleton (RecordExt "A" (Project "A" (Var Stop))
                            (RecordExt "B" (Project "C" (Var Stop))
                            RecordNil)))
                 (Val [])) bigR

  -- boatToursTracePhone : Expr G (TyList (TyRecord (TyRecordExt "name" TyString (TyRecordExt "phone" TyString (TyRecordExt "phone_trace" (TyTraced TyString) TyRecordNil)))))
  -- boatToursTracePhone =
  --   For (For (If ((Op2 (the (interpTy TyString -> interpTy TyString -> Bool) (==))
  --                      (the (Expr _ TyString) (Project "name" (Var (Pop Stop))))
  --                      (the (Expr _ TyString) (Project "name" (Var Stop))))
  --                 && (Op2 (the (interpTy TyString -> interpTy TyString -> Bool) (==))
  --                      (the (Expr _ TyString) (Project "type" (Var Stop)))
  --                      (the (Expr _ TyString) (Val "boat"))))
  --     (Singleton (RecordExt "name" (Project "name" (Var Stop))
  --                (RecordExt "phone" (Project "phone" (Var (Pop Stop)))
  --                (RecordExt "phone_trace" (Trace (Project "phone" (Var (Pop Stop))))
  --                RecordNil))))
  --     (Val [])) eTours) agencies

  -- [["name" := "EdinTours",
  --   "phone" := "412 1200",
  --   "phone_trace" := ("412 1200", TProject "phone" TVar)],
  --  ["name" := "EdinTours",
  --   "phone" := "412 1200",
  --   "phone_trace" := ("412 1200", TProject "phone" TVar)],
  --  ["name" := "Burns's",
  --   "phone" := "607 3000",
  --   "phone_trace" := ("607 3000", TProject "phone" TVar)]]
  -- : List (Record [("name", String), ("phone", String), ("phone_trace", String, ATrace)])

  -- Maybe my intuition that it would make sense to trace a whole
  -- query block wasn't so bad after all. Perhaps we could compute the
  -- full trace, but derive an extraction function from the shape of
  -- the query that, when applied to the trace, projects out the data
  -- and provenance as appropriate. Oh. Maybe that's what James meant
  -- all along and I've been confused all this time. That doesn't even
  -- sound unlikely. Oh my.

  -- Okay, so this is difficult because of functional extensionality problems.
  -- total teval_consistent : (env : Env G) -> (e : Expr G t) -> eval env e = fst (teval env e)
