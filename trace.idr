import Data.Vect
import Data.Fin
import Record

total
mapIndexed : (a -> Nat -> b) -> List a -> List b
mapIndexed f l = go l Z
  where go [] i = []
        go (x :: xs) i = f x i :: go xs (S i)

total fst3 : (a, b, c) -> a
fst3 = fst

total snd3 : (a, b, c) -> b
snd3 = fst . snd

total thd3 : (a, b, c) -> c
thd3 = snd . snd

data ATrace = TVar | TVal t | TLam | TApp ATrace ATrace | TOp1 ATrace | TOp2 ATrace ATrace
            | TAnd ATrace ATrace -- | TEq ATrace ATrace
            | TIf Bool ATrace ATrace | TTrace
            | TCup ATrace ATrace | TFor ATrace (List (Nat, ATrace)) | TSingleton ATrace | TTable String
            | TRecordNil | TRecordExt String ATrace ATrace | TProject String ATrace

mutual
  data Ty = TyInt | TyBool | TyString | TyList Ty | TyFun Ty Ty | TyTraced Ty
          | TyRecord RTy
  -- Could call these Nil and :: for syntactic sugar
  -- Actually, I tried that, but it confuses the totality checker
  data RTy = TyRecordNil | TyRecordExt String Ty RTy

mutual
  total
  interpTy : Ty -> Type
  interpTy TyInt = Int
  interpTy TyBool = Bool
  interpTy TyString = String
  interpTy (TyList x) = List (interpTy x)
  interpTy (TyFun A T) = interpTy A -> interpTy T
  interpTy (TyTraced t) = (interpTy t, ATrace)
  interpTy (TyRecord rty) = Record {labelType=String} (interpRTy rty)

  total
  interpRTy : RTy -> List (String, Type)
  interpRTy TyRecordNil = []
  interpRTy (TyRecordExt l ty rty) = (l, interpTy ty) :: interpRTy rty

data TyLabelPresent : String -> RTy -> Ty -> Type where
  Here  : TyLabelPresent l (TyRecordExt l ty _) ty
  There : TyLabelPresent l row ty -> TyLabelPresent l (TyRecordExt _ _ row) ty

-- Convert a proof of label presence for object language records to a proof of label presence for idris records so we can use projection from there
objToMetaLabelPresenceProof : TyLabelPresent label row ty -> LabelPresent label (interpRTy row) (interpTy ty)
objToMetaLabelPresenceProof Here = Here
objToMetaLabelPresenceProof (There prf) = There (objToMetaLabelPresenceProof prf)

using (G: Vect n Ty)

  data HasType : (i : Fin n) -> Vect n Ty -> Ty -> Type where
    Stop : HasType FZ (t :: G) t
    Pop : HasType k G t -> HasType (FS k) (u :: G) t

  data Expr : Vect n Ty -> Ty -> Type where
    Var : HasType i G t -> Expr G t
    Val : interpTy t -> Expr G t
    Lam : Expr (a :: G) t -> Expr G (TyFun a t)
    App : Expr G (TyFun a t) -> Expr G a -> Expr G t
    (&&) : Expr G TyBool -> Expr G TyBool -> Expr G TyBool
    -- Equality is hard... Just eval x == eval y complains about no instance of Eq for (interpTy ty)
    -- One reason could be: ty could be TyFun, in which case interpTy ty is (a -> b) and function equality is notoriously hard...
    -- It's probably possible to constrain t to equatable types somehow. For now, just use Op2 with (==) (which unfortunately needs to be ascribed with the correct type :/)
    -- (==) : Expr G ty -> Expr G ty -> Expr G TyBool
    Op1 : (interpTy a -> interpTy b) -> Expr G a -> Expr G b
    Op2 : (interpTy a -> interpTy b -> interpTy c) -> Expr G a -> Expr G b -> Expr G c
    If  : Expr G TyBool -> Lazy (Expr G a) -> Lazy (Expr G a) -> Expr G a
    Cup : Expr G (TyList a) -> Expr G (TyList a) -> Expr G (TyList a)
    For : Expr (a :: G) (TyList b) -> Expr G (TyList a) -> Expr G (TyList b)
    Singleton : Expr G t -> Expr G (TyList t)
    Trace : Expr G t -> Expr G (TyTraced t)
    Data : Expr G (TyTraced t) -> Expr G t
    -- how to enforce record of flat base types?
    Table : String -> List (interpTy t) -> Expr G (TyList t)
    RecordNil : Expr G (TyRecord TyRecordNil)
    RecordExt : (l : String) -> Expr G t -> Expr G (TyRecord row) -> Expr G (TyRecord (TyRecordExt l t row))
    Project : (l : String) -> Expr G (TyRecord row) -> { auto prf : TyLabelPresent l row ty } -> Expr G ty

  data Env : Vect n Ty -> Type where
    Nil  : Env Nil
    (::) : interpTy a -> Env G -> Env (a :: G)

  total
  lookup : HasType i G t -> Env G -> interpTy t
  lookup Stop (x :: y) = x
  lookup (Pop x) (y :: z) = lookup x z

  total
  teval : Env G -> Expr G t -> (interpTy t, ATrace)
  teval env (Var x) = (lookup x env, TVar)
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
    in (f vx, TOp1 tx)
  teval env (Op2 f x y) =
    let (vx, tx) = teval env x
        (vy, ty) = teval env y
    in (f vx vy, TOp2 tx ty)
  teval env (If x y z) =
    let (vx, tx) = teval env x
    -- Idris thinks the nice version might not be total :(
        -- (ve, te) = teval env (if vx then y else z)
    -- in (ve, TIf vx tx te)
    in if vx then let (vy, ty) = teval env y in (vy, TIf vx tx ty)
             else let (vz, tz) = teval env z in (vz, TIf vx tx tz)
  teval env (Cup x y) =
    let (vx, tx) = teval env x
        (vy, ty) = teval env y
    in (vx ++ vy, TCup tx ty)
  teval env (For body input) =
    let
      (vinput, tinput) = teval env input
      res = mapIndexed (\x => \i => (i, teval (x :: env) body)) vinput
      v = concatMap snd3 res
      t = TFor tinput (map (\p => (fst3 p, thd3 p)) res)
    in (v, t)
  teval env (Singleton x) =
    let (vx, tx) = teval env x
    in ([ vx ], TSingleton tx)
  -- TTrace is a bit useless, maybe even harmful? We don't really need or want nested `traced` blocks.
  -- Options: - add more type state to Expr, to track whether we are inside a trace block already.
  --          - can we change interpTy (TyTrace t) to avoid nesting?
  teval env (Trace e) = (teval env e, TTrace)
  teval env (Data e) = fst (teval env e)
  teval env (Table n d) = (d, TTable n)
  teval env RecordNil = ([], TRecordNil)
  teval env (RecordExt l e rec) =
    let (ve, te) = teval env e
        (vr, tr) = teval env rec
    in ((l := ve) :: vr, TRecordExt l te tr)
  teval env (Project l r { prf }) =
    let (vr, tr) = teval env r
    in (project' l vr (objToMetaLabelPresenceProof prf), TProject l tr)

  total
  eval : Env G -> Expr G t -> interpTy t
  eval env (Var x) = lookup x env
  eval env (Val v) = v
  eval env (Lam body) = \x => eval (x :: env) body
  eval env (App f e) = eval env f (eval env e)
  eval env ((&&) x y) = eval env x && eval env y
  -- eval env ((==) x y) = valueEq (eval env x) (eval env y)
  eval env (Op1 f x) = f (eval env x)
  eval env (Op2 op x y) = op (eval env x) (eval env y)
  eval env (If x y z) = if eval env x then eval env y else eval env z
  eval env (Cup x y) = eval env x ++ eval env y
  eval env (For body input) =
    concatMap (\x => eval (x :: env) body) (eval env input)
  eval env (Singleton x) = [ eval env x ]
  eval env (Trace e) = teval env e
  eval env (Data e) = fst (eval env e)
  eval env (Table _ d) = d
  eval env RecordNil = []
  eval env (RecordExt l e rec) = (l := eval env e) :: eval env rec
  eval env (Project l r { prf }) = project' l (eval env r) (objToMetaLabelPresenceProof prf)

  one : Expr G TyInt
  one = Val 1

  incr : Expr G (TyFun TyInt TyInt)
  incr = Lam (Op2 (+) (Var Stop) one)

  l12345 : Expr G (TyList TyInt)
  l12345 = Val [ 1, 2, 3, 4, 5 ]

  l23456 : Expr G (TyList TyInt)
  l23456 = Op2 map incr l12345

  l34567 : Expr G (TyList TyInt)
  l34567 = For (Singleton (Op2 (+) (Var Stop) one)) l23456

  l357 : Expr G (TyList TyInt)
  l357 = For (If (Op2 (\x => \y => mod x 2 == y) (Var Stop) one) (Singleton (Var Stop)) (Val [])) l34567

  multl12l23 : Expr G (TyList TyInt)
  multl12l23 = For (For (Singleton (Op2 (*) (Var Stop) (Var (Pop Stop)))) l23456) l12345

  traceMult : Expr G (TyTraced (TyList TyInt))
  traceMult = Trace multl12l23

  -- should be equal to multl12l23
  dataTraceMult : Expr G (TyList TyInt)
  dataTraceMult = Data traceMult

  a2 : Expr G (TyRecord (TyRecordExt "a" TyInt TyRecordNil))
  a2 = RecordExt "a" (Op2 (+) one one) RecordNil

  true : Expr G TyBool
  true = Val True

  a2bTrue : Expr G (TyRecord (TyRecordExt "b" TyBool (TyRecordExt "a" TyInt TyRecordNil)))
  a2bTrue = RecordExt "b" true a2

  a2bTruePa : Expr G TyInt
  a2bTruePa = Project "a" a2bTrue

  agencies : Expr G (TyList (TyRecord (TyRecordExt "name" TyString (TyRecordExt "based_in" TyString (TyRecordExt "phone" TyString TyRecordNil)))))
  agencies = Table "agencies"
    [ [ "name" := "EdinTours", "based_in" := "Edinburgh", "phone" := "412 1200" ],
      [ "name" := "Burns's", "based_in" := "Glasgow", "phone" := "607 3000" ] ]

  eTours : Expr G (TyList (TyRecord (TyRecordExt "name" TyString (TyRecordExt "destination" TyString (TyRecordExt "type" TyString (TyRecordExt "price" TyInt TyRecordNil))))))
  eTours = Table "externalTours"
    [ [ "name" := "EdinTours", "destination" := "Edinburgh", "type" := "bus", "price" := 20 ],
      [ "name" := "EdinTours", "destination" := "Loch Ness", "type" := "bus", "price" := 50 ],
      [ "name" := "EdinTours", "destination" := "och Ness", "type" := "boat", "price" := 200 ],
      [ "name" := "EdinTours", "destination" := "Firth of Forth", "type" := "boat", "price" := 50 ],
      [ "name" := "Burns's", "destination" := "Islay", "type" := "boat", "price" := 100 ],
      [ "name" := "Burns's", "destination" := "Mallaig", "type" := "train", "price" := 40 ] ]

  boatTours : Expr G (TyList (TyRecord (TyRecordExt "name" TyString (TyRecordExt "phone" TyString TyRecordNil))))
  boatTours =
    For (For (If ((Op2 (the (interpTy TyString -> interpTy TyString -> Bool) (==))
                       (the (Expr _ TyString) (Project "name" (Var (Pop Stop))))
                       (the (Expr _ TyString) (Project "name" (Var Stop))))
                  && (Op2 (the (interpTy TyString -> interpTy TyString -> Bool) (==))
                       (the (Expr _ TyString) (Project "type" (Var Stop)))
                       (the (Expr _ TyString) (Val "boat"))))
      (Singleton (RecordExt "name" (Project "name" (Var Stop)) (RecordExt "phone" (Project "phone" (Var (Pop Stop))) RecordNil)))
      (Val [])) eTours) agencies

  boatToursTracePhone : Expr G (TyList (TyRecord (TyRecordExt "name" TyString (TyRecordExt "phone" TyString (TyRecordExt "phone_trace" (TyTraced TyString) TyRecordNil)))))
  boatToursTracePhone =
    For (For (If ((Op2 (the (interpTy TyString -> interpTy TyString -> Bool) (==))
                       (the (Expr _ TyString) (Project "name" (Var (Pop Stop))))
                       (the (Expr _ TyString) (Project "name" (Var Stop))))
                  && (Op2 (the (interpTy TyString -> interpTy TyString -> Bool) (==))
                       (the (Expr _ TyString) (Project "type" (Var Stop)))
                       (the (Expr _ TyString) (Val "boat"))))
      (Singleton (RecordExt "name" (Project "name" (Var Stop))
                 (RecordExt "phone" (Project "phone" (Var (Pop Stop)))
                 (RecordExt "phone_trace" (Trace (Project "phone" (Var (Pop Stop))))
                 RecordNil))))
      (Val [])) eTours) agencies

  -- [["name" := "EdinTours",
  --   "phone" := "412 1200",
  --   "phone_trace" := ("412 1200", TProject "phone" TVar)],
  --  ["name" := "EdinTours",
  --   "phone" := "412 1200",
  --   "phone_trace" := ("412 1200", TProject "phone" TVar)],
  --  ["name" := "Burns's",
  --   "phone" := "607 3000",
  --   "phone_trace" := ("607 3000", TProject "phone" TVar)]]
  -- : List (Record [("name", String), ("phone", String), ("phone_trace", String, ATrace)])

  -- Maybe my intuition that it would make sense to trace a whole
  -- query block wasn't so bad after all. Perhaps we could compute the
  -- full trace, but derive an extraction function from the shape of
  -- the query that, when applied to the trace, projects out the data
  -- and provenance as appropriate. Oh. Maybe that's what James meant
  -- all along and I've been confused all this time. That doesn't even
  -- sound unlikely. Oh my.

  -- Okay, so this is difficult because of functional extensionality problems.
  -- total teval_consistent : (env : Env G) -> (e : Expr G t) -> eval env e = fst (teval env e)
