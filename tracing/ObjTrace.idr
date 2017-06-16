module ObjTrace

import Expr
import Ty
import Data.Vect

%default total

traceType : Nat -> (Ty n) -> (Ty n)
traceType Z t =
  TyVariant
  (TyVariantExt "var" TyString
  (TyVariantExt "val" t
  TyVariantNil))
traceType (S k) t =
  TyVariant
  (TyVariantExt "var" TyString
  (TyVariantExt "val" t
  (TyVariantExt "and" (TyRecord (TyRecordExt "left" (traceType k TyBool)
                                (TyRecordExt "right" (traceType k TyBool) TyRecordNil)))
  TyVariantNil)))

-- traceDepth : {G : Vect en Ty s} -> Expr G t -> Nat

-- selfTrace : {G : Vect en Ty} -> (p : Expr G t) -> Expr G (traceType (traceDepth p) t)

-- This looks like it might require existential types or something in the object language types.
-- Let's try a different approach: a trace type custom-made for every program.

-- traceType' : {G : Vect en Ty} -> (p : Expr G t) -> Ty
-- traceType' (Var x) = ?traceType'_rhs_1
-- traceType' (Val {t} _) = traceType?traceType'_rhs_2
-- traceType' (Lam x) = ?traceType'_rhs_3
-- traceType' (App x y) = ?traceType'_rhs_4
-- traceType' (x + y) = ?traceType'_rhs_5
-- traceType' (x && y) = ?traceType'_rhs_6
-- traceType' (x == y) = ?traceType'_rhs_7
-- traceType' (If x y z) = ?traceType'_rhs_8
-- traceType' (Cup x y) = ?traceType'_rhs_9
-- traceType' (For x y) = ?traceType'_rhs_10
-- traceType' (Singleton x) = ?traceType'_rhs_11
-- traceType' (Table x xs) = ?traceType'_rhs_12
-- traceType' RecordNil = ?traceType'_rhs_13
-- traceType' (RecordExt l x y) = ?traceType'_rhs_14
-- traceType' (Project l x) = ?traceType'_rhs_15
-- traceType' (Constr l x) = ?traceType'_rhs_16
-- traceType' (Match x y) = ?traceType'_rhs_17

-- selfTrace' : {G : Vect en Ty} -> (p : Expr G t) -> Expr G (traceType' p)
-- selfTrace' p = ?selfTrace'_rhs
