module Ty

%access public export
%default total

mutual
  data Ty = TyInt | TyBool | TyString
          | TyList Nat Ty
          | TyFun Ty Ty
          | TyRecord RTy
          | TyVariant VTy
  data RTy = TyRecordNil | TyRecordExt String Ty RTy
  data VTy = TyVariantNil | TyVariantExt String Ty VTy

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

-- This has a different order of arguments!
namespace Variants
  data TyLabelPresent : String -> Ty -> VTy -> Type where
    Here  : TyLabelPresent l t (TyVariantExt l t _)
    There : TyLabelPresent l t v -> TyLabelPresent l t (TyVariantExt _ _ v)

  

