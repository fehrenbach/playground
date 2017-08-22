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

total
projectL : interpTy (everyLinTy (TyRecord r)) -> (l : String) -> TyLabelPresent l r ty -> interpTy (everyLinTy ty)
projectL ((_ := x) :: y) l Here = x
projectL (x :: y) l (There w) = projectL y l w


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
  everyLin env (TFor {n} {m} {b} inTrace inValues outTraces) =
   let inLin = everyLin env inTrace
       f = \(ln, r) => let
           relatedOutTraces = filter (\(l, _) => l == ln) outTraces
         in concat (map (\(_, t) => map (\(lm, rb) => (ln ++ lm, [ "data" := rb . "data"
                                                                 , "prov" := rb . "prov" ++ r . "prov" ]))
                                        (everyLin (r . "data" :: env) 
                                                  (assert_smaller (TFor inTrace inValues outTraces) t)))
                        relatedOutTraces)
   in concat (map f inLin)
  everyLin env (TIf _ _ z) = everyLin env z
  everyLin env (TSingleton x _) = [([], ["data" := everyLin env x, "prov" := []])]
  everyLin env TRecordNil = []
  everyLin env (TRecordExt l xt _ rt _) =
    (l := everyLin env xt) :: everyLin env rt
  everyLin env (TProject l x _ {prf}) =
    projectL (everyLin env x) l prf
  everyLin env TLam = ?rhs_3
  everyLin env (TApp x y) = ?rhs_4
  everyLin env (TOp1 x) = ?rhs_5
  everyLin env (TOp2 x y) = ?rhs_6
  everyLin env (TAnd x y) = ?rhs_7
  everyLin env (TCup x y) = ?rhs_9
  everyLin env (TEq x y) = ?rhs_10
