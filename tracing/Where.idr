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

  total
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

total -- This is a lie. It's not total, but seems easier than dealing with partiality at every call site
findPrefix : Vect n Nat -> List (Vect n Nat, a) -> a
findPrefix xs [] = ?canthappenimsureofit
findPrefix xs ((xl, res) :: ys) = if xs == xl then res else findPrefix xs ys

using (G: Vect en Ty)
  namespace WhereEnv
    data WhereEnv : Vect en Ty -> Type where
      Nil  : WhereEnv Nil
      (::) : interpTy (everyWhereTy a) -> WhereEnv G -> WhereEnv (a :: G)

    total
    lookup : HasType i G t -> WhereEnv G -> interpTy (everyWhereTy t)
    lookup Stop (x :: _) = x
    lookup (Pop x) (_ :: y) = lookup x y

  total
  addFakeProv : (t: Ty) -> interpTy t -> interpTy (everyWhereTy t)
  addFakeProv TyInt x = [ "data" := x, "row" := (-1), "table" := "fake", "column" := "news" ]
  addFakeProv TyBool x = [ "data" := x, "row" := (-1), "table" := "fake", "column" := "news" ]
  addFakeProv TyString x = [ "data" := x, "row" := (-1), "table" := "fake", "column" := "news" ]
  addFakeProv (TyList k y) x = map (\(l, v) => (l, addFakeProv _ v)) x
  addFakeProv (TyFun y z) x = ?addFakeProv_rhs_6
  addFakeProv (TyRecord y) x = ?addFakeProv_rhs_7

  total
  projectW : interpTy (everyWhereTy (TyRecord r)) -> (l : String) -> TyLabelPresent l r ty -> interpTy (everyWhereTy ty)
  projectW ((_ := x) :: y) l Here = x
  projectW (x :: y) l (There w) = projectW y l w

  total
  everyWhere : {ty: Ty} -> WhereEnv G -> interpTy ty -> ATrace G ty -> interpTy (everyWhereTy ty)
  everyWhere env v (TVar var) = lookup var env
  everyWhere {ty} env v (TVal x) = addFakeProv ty x
  everyWhere env v (TIf x y z) = everyWhere env v z
  everyWhere env v (TFor {n} {m} {b} inTrace inValues outTraces) =
    let
      inWhere = everyWhere env inValues inTrace
      f = \(nmL, outV) =>
        let (nL, mL) = splitAt n nmL
            outT     = findPrefix nL outTraces
            outWS    = everyWhere (findPrefix nL inWhere :: env)
                                  (the (interpTy (TyList m b)) [(mL, outV)])
                                  (assert_smaller (TFor inTrace inValues outTraces) outT)
            -- We know outWS will be a singleton list, because of the prefix code business,
            -- but we can avoid using the non-total `unsingleton : List a -> a`
        in map (\(_, outW) => (nmL, outW)) outWS
    in concat (map f v)
  everyWhere env v (TSingleton {n} t inV) =
    [(replicate n 0, everyWhere env inV t)]
  everyWhere env v (TTable name _ {prf}) =
    mapIndexed (\x => (\i => ([i], initialTableRecordWhereProv name prf (snd x) i))) v
  everyWhere env v TRecordNil = []
  everyWhere env v (TRecordExt l xt xv rt rv) =
    (l := everyWhere env xv xt) :: everyWhere env rv rt
  everyWhere env v (TProject x y z {prf}) =
    projectW (everyWhere env z y) x prf
  everyWhere env v _ = ?todo
  -- everyWhere env v TLam = ?everyWhere_rhs_3
  -- everyWhere env v (TApp x y) = ?everyWhere_rhs_4
  -- everyWhere env v (TOp1 x) = ?everyWhere_rhs_5
  -- everyWhere env v (TOp2 x y) = ?everyWhere_rhs_6
  -- everyWhere env v (TAnd x y) = ?everyWhere_rhs_7
  -- everyWhere env v (TCup x y) = ?everyWhere_rhs_9


  total
  whereProv : Expr [] t -> interpTy (everyWhereTy t)
  whereProv e = let (v, t) = teval [] e
                in everyWhere [] v t

  -- whereProv boatTours
