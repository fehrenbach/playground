module Lineage

import Data.Vect
import Record
import Ty
import Expr
import Trace

%access public export

%default total

mutual
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

  everyLinTyRecord : RTy -> RTy
  everyLinTyRecord TyRecordNil = TyRecordNil
  everyLinTyRecord (TyRecordExt l t r) = TyRecordExt l (everyLinTy t) (everyLinTyRecord r)

  -- Uh, one of Idris or mayself is confused...
  almostId : Record (interpRTy row) -> Record (interpRTy (everyLinTyRecord row))
  almostId [] impossible
  almostId (_ :: _) impossible

using (G: Vect en Ty)
  namespace LinEnv
    data LinEnv : Vect en Ty -> Type where
      Nil  : LinEnv Nil
      (::) : interpTy (everyLinTy a) -> LinEnv G -> LinEnv (a :: G)

    total
    lookup : HasType i G t -> LinEnv G -> interpTy (everyLinTy t)
    lookup Stop (x :: _) = x
    lookup (Pop x) (_ :: y) = lookup x y
    
  everyLin : {ty: Ty} -> LinEnv G -> ATrace G ty -> interpTy (everyLinTy ty)
  everyLin env (TVar x) = lookup x env
  everyLin env (TVal x) = ?addfakeprov
  everyLin env (TTable {prf} name values) = 
    map (\(l, v) => (l, [ "data" := almostId v,
                          "prov" := [ ([], [ "table" := name, "row" := cast (head l) ]) ]]))
        values
  everyLin env TLam = ?rhs_3
  everyLin env (TApp x y) = ?rhs_4
  everyLin env (TOp1 x) = ?rhs_5
  everyLin env (TOp2 x y) = ?rhs_6
  everyLin env (TAnd x y) = ?rhs_7
  everyLin env (TIf x y z) = ?rhs_8
  everyLin env (TCup x y) = ?rhs_9
  everyLin env (TFor x xs ys) = ?rhs_10
  everyLin env (TSingleton x y) = ?rhs_11
  everyLin env TRecordNil = ?rhs_13
  everyLin env (TRecordExt l x y z w) = ?rhs_14
  everyLin env (TProject l x y) = ?rhs_15
