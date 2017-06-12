module Ty

import Data.Fin

%access public export
%default total

mutual
  -- Indexed by the number of type variables
  data Ty : Nat -> Type where
    TyInt : Ty 0
    TyBool : Ty 0
    TyString : Ty 0
    TyList : Nat -> Ty s -> Ty s
    TyFun : Ty s -> Ty s -> Ty s
    TyVar : Fin s -> Ty s
    TyForall : Ty (S s) -> Ty s
    TyRecord : RTy s -> Ty s
    TyVariant : VTy s -> Ty s
  data RTy : Nat -> Type where
    TyRecordNil : RTy s
    TyRecordExt : String -> Ty s -> RTy s -> RTy s
  data VTy : Nat -> Type where
    TyVariantNil : VTy s
    TyVariantExt : String -> Ty s -> VTy s -> VTy s

forallaa : Ty 0
forallaa = TyForall (TyVar 0)

PolyId : Ty 0
PolyId = TyForall (TyFun (TyVar 0) (TyVar 0))

polyCompose : Ty 0
polyCompose = TyForall (TyForall (TyFun (TyForall (TyFun (TyFun (TyVar 0) (TyVar 2)) (TyFun (TyVar 2) (TyVar 1)))) (TyFun (TyVar 0) (TyVar 1))))

OneOrPlusOne : Ty 0
OneOrPlusOne = TyVariant (TyVariantExt "i" TyInt (TyVariantExt "f" (TyFun TyInt TyInt) TyVariantNil))

ETourTy : Ty 0
ETourTy = TyList 1 (TyRecord (TyRecordExt "name" TyString (TyRecordExt "destination" TyString (TyRecordExt "type" TyString (TyRecordExt "price" TyInt TyRecordNil)))))

Show (Ty n) where
  show TyInt = "Int"
  show TyBool = "Bool"
  show TyString = "String"
  show (TyList _ t) = "[" ++ show t ++ "]"
  show (TyFun a b) = "(" ++ show a ++ " -> " ++ show b ++ ")"
  show (TyVar FZ) = "a" -- "α"
  show (TyVar (FS FZ)) = "b" -- "β"
  show (TyVar (FS (FS FZ))) = "c" -- "γ"
  show (TyVar v) = "t_" ++ show (finToInteger v)  -- "τ_" -- ++ show v
  show (TyForall {s = Z} t) = "forall a. " ++ show t ++ "" -- "∀ ." ++ show t
  show (TyForall {s = S Z} t) = "forall b. " ++ show t ++ "" -- "∀ ." ++ show t
  show (TyForall {s = S (S Z)} t) = "forall c. " ++ show t ++ "" -- "∀ ." ++ show t
  show (TyForall {s = k} t) = "forall t_" ++ show t ++ ". " ++ show t ++ "" -- "∀ ." ++ show t
  show (TyRecord rty) = "{" ++ rows rty ++ "}"
    where rows TyRecordNil = ""
          rows (TyRecordExt l t TyRecordNil) = l ++ " : " ++ show t
          rows (TyRecordExt l t row) = l ++ " : " ++ show t ++ ", " ++ (rows row)
  show (TyVariant vty) = "[| " ++ variants vty ++ " |]"
    where variants TyVariantNil = ""
          variants (TyVariantExt l t TyVariantNil) = l ++ " : " ++ show t
          variants (TyVariantExt l t vty) = l ++ " : " ++ show t ++ " | " ++ (variants vty)

data TyLabelPresent : String -> Ty s -> RTy s -> Type where
  Here  : TyLabelPresent l ty (TyRecordExt l ty _)
  There : TyLabelPresent l ty row -> TyLabelPresent l ty (TyRecordExt _ _ row)

data IsBaseType : Ty s -> Type where
  IntIsBase : IsBaseType TyInt
  BoolIsBase : IsBaseType TyBool
  StringIsBase : IsBaseType TyString

data IsBaseRow : RTy s -> Type where
  EmptyRowIsBase : IsBaseRow TyRecordNil
  ExtRowIsBase : IsBaseType ty -> IsBaseRow row -> IsBaseRow (TyRecordExt _ ty row)

-- This has a different order of arguments!
namespace Variants
  data TyLabelPresent : String -> Ty s -> VTy s -> Type where
    Here  : TyLabelPresent l t (TyVariantExt l t _)
    There : TyLabelPresent l t v -> TyLabelPresent l t (TyVariantExt _ _ v)
