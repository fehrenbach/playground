module Lineage

import Data.Vect
import Record
import Ty
import Expr
import Trace

%access public export
%default total

mutual
  total
  everyLinTy : Ty -> Ty
  everyLinTy TyInt = TyInt
  everyLinTy TyBool = TyBool
  everyLinTy TyString = TyString
  everyLinTy (TyList k x) = TyList k (TyRecord (TyRecordExt "data" (everyLinTy x)
                                               (TyRecordExt "prov"
                                                  (TyList 0 (TyRecord (TyRecordExt "table" TyString 
                                                                      (TyRecordExt "row" TyInt 
                                                                       TyRecordNil))))
                                                TyRecordNil)))
  everyLinTy (TyFun x y) = ?everyLinTyFun
  everyLinTy (TyRecord r) = TyRecord (everyLinTyRecord r)

  total
  everyLinTyRecord : RTy -> RTy
  everyLinTyRecord TyRecordNil = TyRecordNil
  everyLinTyRecord (TyRecordExt l t r) = TyRecordExt l (everyLinTy t) (everyLinTyRecord r)

mutual
  total
  addEmptyProvenance : interpTy ty -> interpTy (everyLinTy ty)
  addEmptyProvenance {ty = TyInt} x = x
  addEmptyProvenance {ty = TyBool} x = x
  addEmptyProvenance {ty = TyString} x = x
  addEmptyProvenance {ty = (TyList k y)} x = map (\(l, v) => (l, [ "data" := addEmptyProvenance v,
                                                                   "prov" := [] ])) x
  addEmptyProvenance {ty = (TyFun y z)} x = ?addEmptyProvenance_rhs_6
  addEmptyProvenance {ty = (TyRecord y)} x = addEmptyProvenanceRecord x

  total
  addEmptyProvenanceRecord : Record (interpRTy r) -> Record (interpRTy (everyLinTyRecord r))
  addEmptyProvenanceRecord {r = TyRecordNil} [] = []
  addEmptyProvenanceRecord {r = (TyRecordExt x y z)} ((x := w) :: s) = (x := addEmptyProvenance w) :: addEmptyProvenanceRecord s

using (G: Vect en Ty)
  namespace LinEnv
    data LinEnv : Vect en Ty -> Type where
      Nil  : LinEnv Nil
      (::) : interpTy (everyLinTy a) -> LinEnv G -> LinEnv (a :: G)

    total
    lookup : HasType i G t -> LinEnv G -> interpTy (everyLinTy t)
    lookup Stop (x :: _) = x
    lookup (Pop x) (_ :: y) = lookup x y
    
  -- this uses another approach, namely reevaluating the query according to the trace
  everyLin : {ty: Ty} -> LinEnv G -> ATrace G ty -> interpTy (everyLinTy ty)
  everyLin env (TVar x) = lookup x env
  everyLin env (TVal x) = addEmptyProvenance x
  everyLin env (TTable {prf} name values) = 
    map (\(l, v) => (l, [ "data" := addEmptyProvenanceRecord v,
                          "prov" := [ ([], [ "table" := name, "row" := cast (head l) ]) ]]))
        values
  everyLin env (TFor inTrace inValues outTraces) =
   let inLin = everyLin env inTrace
       f = \(ln, r) => ?listOfAnnotatedMStuff
   in concat (map f inLin)
  everyLin env TLam = ?rhs_3
  everyLin env (TApp x y) = ?rhs_4
  everyLin env (TOp1 x) = ?rhs_5
  everyLin env (TOp2 x y) = ?rhs_6
  everyLin env (TAnd x y) = ?rhs_7
  everyLin env (TIf x y z) = ?rhs_8
  everyLin env (TCup x y) = ?rhs_9
  everyLin env (TSingleton x y) = ?rhs_11
  everyLin env TRecordNil = ?rhs_13
  everyLin env (TRecordExt l x y z w) = ?rhs_14
  everyLin env (TProject l x y) = ?rhs_15
