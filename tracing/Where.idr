module Where

import Data.Vect
import Record
import Ty
import Expr
import Trace

%access public export

%default total
      
total
whereTy : Ty -> Ty
whereTy t = TyRecord (TyRecordExt "data" t
                     (TyRecordExt "row" TyInt
                     (TyRecordExt "table" TyString
                     (TyRecordExt "column" TyString
                     TyRecordNil))))
mutual
  total
  everyWhereTy : Ty -> Ty
  everyWhereTy TyInt = whereTy TyInt
  everyWhereTy TyBool = whereTy TyBool
  everyWhereTy TyString = whereTy TyString
  everyWhereTy (TyList n x) = TyList n (everyWhereTy x)
  everyWhereTy (TyFun x y) = TyFun (everyWhereTy x) (everyWhereTy y)
  everyWhereTy (TyRecord r) = TyRecord (everyWhereTyRecord r)

  everyWhereTyRecord : RTy -> RTy
  everyWhereTyRecord TyRecordNil = TyRecordNil
  everyWhereTyRecord (TyRecordExt l t r) = TyRecordExt l (everyWhereTy t) (everyWhereTyRecord r)
  
mutual
  total
  initialTableRecordWhereProv : {row : RTy} -> String -> (prf : IsBaseRow row) -> Record (interpRTy row) -> Nat -> Record (interpRTy (everyWhereTyRecord row))
  initialTableRecordWhereProv x EmptyRowIsBase y k = []
  initialTableRecordWhereProv x (ExtRowIsBase w s) ((label := value) :: rest) k = case w of
    -- Yes, it's the exact same thing on the right hand side of all of these, but Idris complains otherwise...
    IntIsBase =>    (label := [ "data" := value, "row" := cast k, "table" := x, "column" := label]) :: initialTableRecordWhereProv x s rest k
    BoolIsBase =>   (label := [ "data" := value, "row" := cast k, "table" := x, "column" := label]) :: initialTableRecordWhereProv x s rest k
    StringIsBase => (label := [ "data" := value, "row" := cast k, "table" := x, "column" := label]) :: initialTableRecordWhereProv x s rest k

total
findPrefix : Vect n Nat -> List (Vect n Nat, a) -> a
findPrefix xs [] = ?canthappenimsureofit
findPrefix xs ((xl, res) :: ys) = if xs == xl then res else findPrefix xs ys

using (G: Vect en Ty)
  total
  findTraceElement : Vect m Nat -> ATrace G (TyList m b) -> ATrace G b
  -- findTraceElement mL (TVar x) = ?findTraceElement_rhs_1
  -- findTraceElement mL (TVal x) = ?findTraceElement_rhs_2
  -- findTraceElement mL TLam = ?findTraceElement_rhs_3
  -- findTraceElement mL (TApp x y) = ?findTraceElement_rhs_4
  -- findTraceElement mL (TOp1 x) = ?findTraceElement_rhs_5
  -- findTraceElement mL (TOp2 x y) = ?findTraceElement_rhs_6
  -- findTraceElement mL (TIf x y z) = ?findTraceElement_rhs_7
  -- findTraceElement mL (TCup x y) = ?findTraceElement_rhs_8
  findTraceElement nmL (TFor {n=n} x xs ys) =
    let (nL, mL) = splitAt n nmL
        foo = findPrefix nL ys
    in findTraceElement mL (assert_smaller (TFor x xs ys) ?notQuiteFoo) -- this is essentially the same problem as before, right?
  findTraceElement mL (TSingleton x y) = x
  -- findTraceElement mL (TTable x xs) = ?findTraceElement_rhs_11
  -- findTraceElement mL (TProject l x) = ?findTraceElement_rhs_12
  findTraceElement ml _ = ?todoThisIsJustToHaveLessHoles

  namespace WhereEnv
    data WhereEnv : Vect en Ty -> Type where
      Nil  : WhereEnv Nil
      (::) : interpTy (everyWhereTy a) -> WhereEnv G -> WhereEnv (a :: G)
  
    total
    lookup : HasType i G t -> WhereEnv G -> interpTy (everyWhereTy t)
    lookup Stop (x :: _) = x
    lookup (Pop x) (_ :: y) = lookup x y

  everyWhere : {ty : Ty} -> WhereEnv G -> (interpTy ty, ATrace G ty) -> interpTy (everyWhereTy ty)
  everyWhere {ty = ty} env (v, trace) = case trace of
    TVar var => lookup var env
    TVal c => case ty of
      TyInt => [ "data" := c, "row" := (-1), "table" := "fake", "column" := "news" ]
      _ => ?tval
    TSingleton {n=n} t inV => [(replicate n 0, everyWhere env (assert_smaller (v, trace) (inV, t)))]
    TTable n _ {prf} => mapIndexed (\x => (\i => ([i], initialTableRecordWhereProv n prf (snd x) i))) v
    TFor {n=n} inTrace inValues outTraces => let 
        inWhere = everyWhere env (assert_smaller (v, trace) (inValues, inTrace))
      in map (\((nmL, outV), nL, outT) =>
                 let (_, mL) = splitAt n nmL
                 in (nmL, assert_total everyWhere (findPrefix nL inWhere :: env)
                                                  (outV, findTraceElement mL outT)))
             (zip v outTraces)
    _ => ?whatisit
