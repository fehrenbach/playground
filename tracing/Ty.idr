module Ty

%access public export
%default total

mutual
  data Ty = TyInt | TyBool | TyString | TyList Nat Ty | TyFun Ty Ty
          | TyRecord RTy
  data RTy = TyRecordNil | TyRecordExt String Ty RTy

data TyLabelPresent : String -> RTy -> Ty -> Type where
  Here  : TyLabelPresent l (TyRecordExt l ty _) ty
  There : TyLabelPresent l row ty -> TyLabelPresent l (TyRecordExt _ _ row) ty

data IsBaseType : Ty -> Type where
  IntIsBase : IsBaseType TyInt
  BoolIsBase : IsBaseType TyBool
  StringIsBase : IsBaseType TyString

data IsBaseRow : RTy -> Type where
  EmptyRowIsBase : IsBaseRow TyRecordNil
  ExtRowIsBase : IsBaseType ty -> IsBaseRow row -> IsBaseRow (TyRecordExt _ ty row)
