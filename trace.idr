import Data.Vect
import Data.Fin
import Record

%default total

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

total
consLabels : Vect n Nat -> List ((Vect m Nat), t) -> List (Vect (plus n m) Nat, t)
consLabels l [] = []
consLabels l ((ls, v) :: rest) = ((l ++ ls), v) :: consLabels l rest

total
extend : {n, k, m : Nat} -> t -> Vect n t -> plus n k = m -> Vect m t
extend {n = Z}   {k = Z}   {m = Z  } _ _  Refl = []
extend {n = Z}   {k = Z}   {m = S _} _ _  Refl impossible
extend {n = Z}   {k = S _} {m = Z}   _ _  Refl impossible
extend {n = Z}   {k = S j} {m = S j} y xs Refl = y :: extend y xs Refl
extend {n = S _} {k = Z}   {m = Z} _ _ Refl impossible
extend {n = S _} {k = S _} {m = Z} _ _ Refl impossible
extend {n = S j} {k = Z}   {m = S (plus j Z)}     y (x :: xs) Refl = x :: extend y xs Refl
extend {n = S j} {k = S k} {m = S (plus j (S k))} y (x :: xs) Refl = x :: extend y xs Refl


mutual
  data Ty = TyInt | TyBool | TyString | TyList Nat Ty | TyFun Ty Ty
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
  interpTy (TyList n x) = List (Vect n Nat, interpTy x)
  interpTy (TyFun A T) = interpTy A -> interpTy T
  interpTy (TyRecord rty) = Record {labelType=String} (interpRTy rty)

  total
  interpRTy : RTy -> List (String, Type)
  interpRTy TyRecordNil = []
  interpRTy (TyRecordExt l ty rty) = (l, interpTy ty) :: interpRTy rty

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

-- Convert a proof of label presence for object language records to a proof of label presence for idris records so we can use projection from there
objToMetaLabelPresenceProof : TyLabelPresent label row ty -> LabelPresent label (interpRTy row) (interpTy ty)
objToMetaLabelPresenceProof Here = Here
objToMetaLabelPresenceProof (There prf) = There (objToMetaLabelPresenceProof prf)

using (G: Vect en Ty)
  data HasType : (i : Fin en) -> Vect en Ty -> Ty -> Type where
    Stop : HasType FZ (t :: G) t
    Pop : HasType k G t -> HasType (FS k) (u :: G) t

  data ATrace : Ty -> Type where
    -- Probably need an environment too
    TVar : HasType i G ty -> ATrace ty
    TVal : (interpTy ty) -> ATrace ty
    TLam : ATrace ty
    TApp : ATrace (TyFun a b) -> ATrace a -> ATrace b
    TOp1 : {op : interpTy a -> interpTy b} -> ATrace a -> ATrace b
    TOp2 : {op : interpTy a -> interpTy b -> interpTy c} -> ATrace a -> ATrace b -> ATrace c
    TAnd : ATrace TyBool -> ATrace TyBool -> ATrace TyBool
    TIf : Bool -> ATrace TyBool -> ATrace ty -> ATrace ty
    TCup : ATrace (TyList n ty) -> ATrace (TyList m ty) -> ATrace (TyList (S (maximum n m)) ty)
    TFor : ATrace (TyList n a) -> interpTy (TyList n a) -> List (Vect n Nat, ATrace (TyList m b)) -> ATrace (TyList (plus n m) b)
    TSingleton : ATrace ty -> interpTy ty -> ATrace (TyList n ty)
    -- Should these be TyList 0 instead?
    TTable : String -> interpTy (TyList 1 (TyRecord row)) -> {auto prf : IsBaseRow row} -> ATrace (TyList 1 (TyRecord row))
    TRecordNil : ATrace (TyRecord TyRecordNil)
    TRecordExt : (l : String) -> ATrace t -> ATrace (TyRecord row) -> ATrace (TyRecord (TyRecordExt l t row))
    TProject : (l : String) -> ATrace (TyRecord r) -> { auto prf : TyLabelPresent l r ty } -> ATrace ty

  data Expr : Vect en Ty -> Ty -> Type where
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
    Cup : {n, m : Nat}
       -> Expr G (TyList n a) -> {s : Nat} -> { auto sprf : plus n s = maximum n m }
       -> Expr G (TyList m a) -> {t : Nat} -> { auto tprf : plus m t = maximum n m }
       -> Expr G (TyList (S (maximum n m)) a)
    For : Expr (a :: G) (TyList m b) -> Expr G (TyList n a) -> Expr G (TyList (plus n m) b)
    Singleton : Expr G t -> Expr G (TyList 0 t)
    Table : String -> List (interpTy (TyRecord row)) -> { auto prf : IsBaseRow row } -> Expr G (TyList 1 (TyRecord row))
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
  hasTypeToNat : HasType i G t -> Nat
  hasTypeToNat Stop = Z
  hasTypeToNat (Pop x) = S (hasTypeToNat x)

  total
  teval : Env G -> Expr G t -> (interpTy t, ATrace t)
  teval env (Var x) = (lookup x env, TVar x)
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
    in (f vx, TOp1 {op = f} tx)
  teval env (Op2 f x y) =
    let (vx, tx) = teval env x
        (vy, ty) = teval env y
    in (f vx vy, TOp2 {op=f} tx ty)
  teval env (If x y z) =
    let (vx, tx) = teval env x
    -- Idris thinks the nice version might not be total :(
        -- (ve, te) = teval env (if vx then y else z)
    -- in (ve, TIf vx tx te)
    in if vx then let (vy, ty) = teval env y in (vy, TIf vx tx ty)
             else let (vz, tz) = teval env z in (vz, TIf vx tx tz)
  teval env (Cup {a} {n} {m} x {s} {sprf} y {t} {tprf}) =
    let (vx, tx) = teval env x
        (vy, ty) = teval env y
        v = consLabels [1] (map (\(l, x) => (extend 0 l sprf, x)) vx)
         ++ consLabels [2] (map (\(l, y) => (extend 0 l tprf, y)) vy)
        t = TCup tx ty
    in (v, t)
  teval env (For body input) =
    let
      (vinput, tinput) = teval env input
      v = concatMap (\(l, x) => consLabels l (fst (teval (x :: env) body))) vinput
      t = map (\(l, x) => (l, snd (teval (x :: env) body))) vinput
    in (v, TFor tinput vinput t)
  teval env (Singleton x) =
    let (vx, tx) = teval env x
    in ([ ([], vx) ], TSingleton tx vx)
  -- TTrace is a bit useless, maybe even harmful? We don't really need or want nested `traced` blocks.
  -- Options: - add more type state to Expr, to track whether we are inside a trace block already.
  --          - can we change interpTy (TyTrace t) to avoid nesting
  -- teval env (Trace e) = (teval env e, TTrace)
  -- teval env (Data e) = fst (teval env e)
  teval env (Table n d) = (mapIndexed (\x => \i => ([i], x)) d, TTable n (mapIndexed (\x => \i => ([i], x)) d))
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
  eval env (Cup {a} {n} {m} x {s} {sprf} y {t} {tprf}) =
       consLabels [1] (map (\(l, x) => (extend 0 l sprf, x)) (eval env x))
    ++ consLabels [2] (map (\(l, y) => (extend 0 l tprf, y)) (eval env y))
  eval env (For body input) =
    concatMap (\(ln, vi) => consLabels ln (eval (vi :: env) body)) (eval env input)
  eval env (Singleton x) = [ ([], eval env x) ]
  eval env (Table _ d) = mapIndexed (\x => \i => ([i], x)) d
  eval env RecordNil = []
  eval env (RecordExt l e rec) = (l := eval env e) :: eval env rec
  eval env (Project l r { prf }) = project' l (eval env r) (objToMetaLabelPresenceProof prf)

  one : Expr G TyInt
  one = Val 1

  incr : Expr G (TyFun TyInt TyInt)
  incr = Lam (Op2 (+) (Var Stop) one)

  l12345 : Expr G (TyList 1 TyInt)
  l12345 = Val [ ([0], 1), ([1], 2), ([2], 3), ([3], 4), ([4], 5) ]

  l23456 : Expr G (TyList 1 TyInt)
  l23456 = For (Singleton (App incr (Var Stop))) l12345

  l34567 : Expr G (TyList 1 TyInt)
  l34567 = For (Singleton (Op2 (+) (Var Stop) one)) l23456

  partial -- mod is not total, or something
  l357 : Expr G (TyList 1 TyInt)
  l357 = For (If (Op2 (\x => \y => mod x 2 == y) (Var Stop) one) (Singleton (Var Stop)) (Val [])) l34567

  multl12l23 : Expr G (TyList 2 TyInt)
  multl12l23 = For (For (Singleton (Op2 (*) (Var Stop) (Var (Pop Stop)))) l23456) l12345

  -- traceMult : Expr G (TyTraced (TyList TyInt))
  -- traceMult = Trace multl12l23

  -- should be equal to multl12l23
  -- dataTraceMult : Expr G (TyList TyInt)
  -- dataTraceMult = Data traceMult

  a2 : Expr G (TyRecord (TyRecordExt "a" TyInt TyRecordNil))
  a2 = RecordExt "a" (Op2 (+) one one) RecordNil

  true : Expr G TyBool
  true = Val True

  a2bTrue : Expr G (TyRecord (TyRecordExt "b" TyBool (TyRecordExt "a" TyInt TyRecordNil)))
  a2bTrue = RecordExt "b" true a2

  a2bTruePa : Expr G TyInt
  a2bTruePa = Project "a" a2bTrue
  
  agencies : Expr G (TyList 1 (TyRecord (TyRecordExt "name" TyString (TyRecordExt "based_in" TyString (TyRecordExt "phone" TyString TyRecordNil)))))
  agencies = Table "agencies"
    [ [ "name" := "EdinTours", "based_in" := "Edinburgh", "phone" := "412 1200" ],
      [ "name" := "Burns's", "based_in" := "Glasgow", "phone" := "607 3000" ] ]

  eTours : Expr G (TyList 1 (TyRecord (TyRecordExt "name" TyString (TyRecordExt "destination" TyString (TyRecordExt "type" TyString (TyRecordExt "price" TyInt TyRecordNil))))))
  eTours = Table "externalTours"
    [ [ "name" := "EdinTours", "destination" := "Edinburgh", "type" := "bus", "price" := 20 ],
      [ "name" := "EdinTours", "destination" := "Loch Ness", "type" := "bus", "price" := 50 ],
      [ "name" := "EdinTours", "destination" := "och Ness", "type" := "boat", "price" := 200 ],
      [ "name" := "EdinTours", "destination" := "Firth of Forth", "type" := "boat", "price" := 50 ],
      [ "name" := "Burns's", "destination" := "Islay", "type" := "boat", "price" := 100 ],
      [ "name" := "Burns's", "destination" := "Mallaig", "type" := "train", "price" := 40 ] ]

  boatTours : Expr G (TyList 2 (TyRecord (TyRecordExt "name" TyString (TyRecordExt "phone" TyString TyRecordNil))))
  boatTours =
    For (For (If ((Op2 (the (interpTy TyString -> interpTy TyString -> Bool) (==))
                       (the (Expr _ TyString) (Project "name" (Var (Pop Stop))))
                       (the (Expr _ TyString) (Project "name" (Var Stop))))
                  && (Op2 (the (interpTy TyString -> interpTy TyString -> Bool) (==))
                       (the (Expr _ TyString) (Project "type" (Var Stop)))
                       (the (Expr _ TyString) (Val "boat"))))
      (Singleton (RecordExt "name" (Project "name" (Var Stop)) (RecordExt "phone" (Project "phone" (Var (Pop Stop))) RecordNil)))
      (Val [])) eTours) agencies
  
  boatToursTrace : (List (Vect 2 Nat, Record [("name", String), ("phone", String)]), ATrace (TyList 2 (TyRecord (TyRecordExt "name" TyString (TyRecordExt "phone" TyString TyRecordNil)))))
  boatToursTrace = teval [] boatTours
      
  bigR : Expr G (TyList 1 (TyRecord (TyRecordExt "A" TyInt (TyRecordExt "B" TyInt (TyRecordExt "C" TyInt TyRecordNil)))))
  bigR = Table "R" [ [ "A" := 1, "B" := 2, "C" := 7 ]
                   , [ "A" := 2, "B" := 3, "C" := 8 ]
                   , [ "A" := 4, "B" := 3, "C" := 9 ] ]
                   
  bigQ : Expr G (TyList 1 (TyRecord (TyRecordExt "A" TyInt (TyRecordExt "B" TyInt TyRecordNil))))
  bigQ = For (If (Op2 (the (Int -> Int -> Bool) (==))
                      (Project "B" (Var Stop)) (the (Expr _ TyInt) (Val 3)))
                 (Singleton (RecordExt "A" (Project "A" (Var Stop))
                            (RecordExt "B" (Project "C" (Var Stop))
                            RecordNil)))
                 (Val [])) bigR

  -- boatToursTracePhone : Expr G (TyList (TyRecord (TyRecordExt "name" TyString (TyRecordExt "phone" TyString (TyRecordExt "phone_trace" (TyTraced TyString) TyRecordNil)))))
  -- boatToursTracePhone =
  --   For (For (If ((Op2 (the (interpTy TyString -> interpTy TyString -> Bool) (==))
  --                      (the (Expr _ TyString) (Project "name" (Var (Pop Stop))))
  --                      (the (Expr _ TyString) (Project "name" (Var Stop))))
  --                 && (Op2 (the (interpTy TyString -> interpTy TyString -> Bool) (==))
  --                      (the (Expr _ TyString) (Project "type" (Var Stop)))
  --                      (the (Expr _ TyString) (Val "boat"))))
  --     (Singleton (RecordExt "name" (Project "name" (Var Stop))
  --                (RecordExt "phone" (Project "phone" (Var (Pop Stop)))
  --                (RecordExt "phone_trace" (Trace (Project "phone" (Var (Pop Stop))))
  --                RecordNil))))
  --     (Val [])) eTours) agencies

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

total
tracePrefix : Vect m Nat -> ATrace (TyList m a) -> ATrace a
tracePrefix xs (TVar x) = ?tracePrefix_rhs_1
tracePrefix xs (TVal x) = ?tracePrefix_rhs_2
tracePrefix xs TLam = ?tracePrefix_rhs_3
tracePrefix xs (TApp x y) = ?tracePrefix_rhs_4
tracePrefix xs (TOp1 x) = ?tracePrefix_rhs_5
tracePrefix xs (TOp2 x y) = ?tracePrefix_rhs_6
tracePrefix xs (TIf x y z) = ?tracePrefix_rhs_7
tracePrefix xs (TCup x y) = ?tracePrefix_rhs_8
tracePrefix xs (TFor x ys zs) = ?tracePrefix_rhs_9
tracePrefix xs (TSingleton x y) = x
tracePrefix xs (TTable x ys) = ?tracePrefix_rhs_11
tracePrefix xs (TProject l x) = ?tracePrefix_rhs_12

total
findTracePrefix : Vect (plus n m) Nat -> List (Vect n Nat, ATrace (TyList m a)) -> ATrace a
findTracePrefix {n=n} {m=m} nmL tL =
 let (nL, mL) = splitAt n nmL
 in tracePrefix mL (findPrefix nL tL)

using (G: Vect en Ty)
  namespace WhereEnv
    data WhereEnv : Vect en Ty -> Type where
      Nil  : WhereEnv Nil
      (::) : interpTy (everyWhereTy a) -> WhereEnv G -> WhereEnv (a :: G)
  
  everyWhere : {ty : Ty} -> WhereEnv G -> (interpTy ty, ATrace ty) -> interpTy (everyWhereTy ty)
  everyWhere {ty = ty} env (v, trace) = case trace of
    TVar var => ?lookup var env -- ugh, how do I tell Idris that we keep environments in sync?
    TVal c => case ty of
      TyInt => [ "data" := c, "row" := (-1), "table" := "fake", "column" := "news" ]
      _ => ?tval
    TSingleton {n=n} t inV => [(replicate n 0, everyWhere env (assert_smaller (v, trace) (inV, t)))]
    TTable n _ {prf} => mapIndexed (\x => (\i => ([i], initialTableRecordWhereProv n prf (snd x) i))) v
    TFor inTrace inValues outTraces => let 
        inWhere = everyWhere env (assert_smaller (v, trace) (inValues, inTrace))
      in map (\((nmL, outV), nL, outT) =>
                  (nmL, assert_total everyWhere (findPrefix nL inWhere :: env)
                                   (outV, findTracePrefix nmL outTraces)))
             (zip v outTraces)
    _ => ?whatisit
