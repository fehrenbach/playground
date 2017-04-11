module Trace

import Data.Vect
import Record
import Ty
import Expr

%access public export
%default total

using (G: Vect en Ty)
  data ATrace : Vect en Ty -> Ty -> Type where
    TVar
       : HasType i G ty
      -> ATrace G ty
    TVal
       : (interpTy ty)
      -> ATrace G ty
    TLam
       : ATrace G ty
    TApp
       : ATrace G (TyFun a b)
      -> ATrace G a
      -> ATrace G b
    TOp1
       : {op : interpTy a -> interpTy b}
      -> ATrace G a
      -> ATrace G b
    TOp2
       : {op : interpTy a -> interpTy b -> interpTy c}
      -> ATrace G a
      -> ATrace G b
      -> ATrace G c
    TAnd
       : ATrace G TyBool
      -> ATrace G TyBool
      -> ATrace G TyBool
    TIf
       : Bool
      -> ATrace G TyBool
      -> ATrace G ty
      -> ATrace G ty
    TCup
       : ATrace G (TyList n ty)
      -> ATrace G (TyList m ty)
      -> ATrace G (TyList (S (maximum n m)) ty)
    TFor
       : ATrace G (TyList n a)
      -> interpTy (TyList n a)
      -> List (Vect n Nat, ATrace (a :: G) (TyList m b))
      -> ATrace G (TyList (plus n m) b)
    TSingleton
       : ATrace G ty
      -> interpTy ty
      -> ATrace G (TyList n ty)
    TTable
       : String
      -> interpTy (TyList 1 (TyRecord row))
      -> {auto prf : IsBaseRow row}
      -> ATrace G (TyList 1 (TyRecord row))
    TRecordNil
       : ATrace G (TyRecord TyRecordNil)
    TRecordExt
       : (l : String)
      -> ATrace G t
      -> interpTy t
      -> ATrace G (TyRecord row)
      -> interpTy (TyRecord row)
      -> ATrace G (TyRecord (TyRecordExt l t row))
    TProject
       : (l : String)
      -> ATrace G (TyRecord r)
      -> interpTy (TyRecord r)
      -> { auto prf : TyLabelPresent l r ty }
      -> ATrace G ty

  total
  teval : Env G -> Expr G t -> (interpTy t, ATrace G t)
  teval env (Var x) = (lookup x env, TVar x)
  teval env (Val x) = (x, TVal x)
  teval env (Lam e) = (\x => fst (teval (x :: env) e), TLam)
  teval env (App f a) =
    let (vf, tf) = teval env f
        (va, ta) = teval env a
    in (vf va, TApp tf ta)
  teval env ((&&) x y) =
    let (vx, tx) = teval env x
        (vy, ty) = teval env y
    in (vx && vy, TAnd tx ty)
  teval env (Op1 f x) =
    let (vx, tx) = teval env x
    in (f vx, TOp1 {op = f} tx)
  teval env (Op2 f x y) =
    let (vx, tx) = teval env x
        (vy, ty) = teval env y
    in (f vx vy, TOp2 {op=f} tx ty)
  teval env (If x y z) =
    let (vx, tx) = teval env x
    -- Idris thinks the nice version might not be total :(
        -- (ve, te) = teval env (if vx then y else z)
    -- in (ve, TIf vx tx te)
    in if vx then let (vy, ty) = teval env y in (vy, TIf vx tx ty)
             else let (vz, tz) = teval env z in (vz, TIf vx tx tz)
  teval env (Cup {a} {n} {m} x {s} {sprf} y {t} {tprf}) =
    let (vx, tx) = teval env x
        (vy, ty) = teval env y
        v = consLabels [1] (map (\(l, x) => (extend 0 l sprf, x)) vx)
         ++ consLabels [2] (map (\(l, y) => (extend 0 l tprf, y)) vy)
        t = TCup tx ty
    in (v, t)
  teval env (For body input) =
    let
      (vinput, tinput) = teval env input
      v = concatMap (\(l, x) => consLabels l (fst (teval (x :: env) body))) vinput
      t = map (\(l, x) => (l, snd (teval (x :: env) body))) vinput
    in (v, TFor tinput vinput t)
  teval env (Singleton x) =
    let (vx, tx) = teval env x
    in ([ ([], vx) ], TSingleton tx vx)
  teval env (Table n d) = (mapIndexed (\x => \i => ([i], x)) d, TTable n (mapIndexed (\x => \i => ([i], x)) d))
  teval env RecordNil = ([], TRecordNil)
  teval env (RecordExt l e rec) =
    let (ve, te) = teval env e
        (vr, tr) = teval env rec
    in ((l := ve) :: vr, TRecordExt l te ve tr vr)
  teval env (Project l r { prf }) =
    let (vr, tr) = teval env r
    in (project' l vr (objToMetaLabelPresenceProof prf), TProject l tr vr)


  -- boatToursTrace : (List (Vect 2 Nat, Record [("name", String), ("phone", String)]), ATrace [] (TyList 2 (TyRecord (TyRecordExt "name" TyString (TyRecordExt "phone" TyString TyRecordNil)))))
  -- boatToursTrace = teval [] boatTours
