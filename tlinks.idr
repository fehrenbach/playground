%default total

mutual
data Base =
  BBool | BInt

data C : Type where
  CBase : Base -> C
  CList : C -> C
  CTrace : Base -> C

mutual -- Is this induction-recursion?h
  data Trace : Base -> Type where
    Lit : T (CBase b) -> Trace b
    For : (d: C) -> T (TRACE d) -> Trace b -> Trace b
    If : Trace BBool -> Trace b -> Trace b -> Trace b

  total
  T : C -> Type
  T (CBase BBool) = Bool
  T (CBase BInt) = Int
  T (CList a) = List (T a)
  T (CTrace b) = Trace b
  
  total
  TRACE : C -> C
  TRACE (CBase b) = CTrace b
  TRACE (CList a) = CList (TRACE a)
  TRACE (CTrace b) = CTrace b

total
VALUE : C -> C
VALUE (CBase b) = CBase b
VALUE (CList a) = CList (VALUE a)
VALUE (CTrace b) = CBase b

total
value : (a: C) -> T a -> T (VALUE a)
value (CBase _) x = x
value (CList b) xs = map (value b) xs
value (CTrace b) (Lit l) = l
value (CTrace b) (For c i o) =
  value (CTrace b) o
value (CTrace b) (If c t e) =
  if value (CTrace BBool) c
  then value (CTrace b) t
  else value (CTrace b) e

total
trace_idempotent : (a: C) -> TRACE a = TRACE (TRACE a)
trace_idempotent (CBase x) = Refl
trace_idempotent (CList x) = cong (trace_idempotent x)
trace_idempotent (CTrace x) = Refl

-- so, that's not true, because if a = CTrace x for some x, then the
-- left side turns it into a base type. However, we only really want
-- to consider plain Links query types anyway (so no function types,
-- no Trace)

-- value_trace_id : (a: C) -> VALUE (TRACE a) = a
-- value_trace_id (CBase x) = Refl
-- value_trace_id (CList x) = cong (value_trace_id x)
-- value_trace_id (CTrace x) = ?nope -- uh, this looks like it's just plain wrong

data IsQueryType : C -> Type where
  BaseIsQueryType : IsQueryType (CBase b)
  ListIsQueryType : IsQueryType a -> IsQueryType (CList a)

-- That's true, very good.
total
value_trace_id : (a: C) -> IsQueryType a -> VALUE (TRACE a) = a
value_trace_id (CBase x) _ = Refl
value_trace_id (CList y) (ListIsQueryType x) = cong (value_trace_id y x)
value_trace_id (CTrace _) BaseIsQueryType impossible
value_trace_id (CTrace _) (ListIsQueryType _) impossible

total
TypeRec : (a : C) -> (Base -> C) -> (Base -> C) -> (C -> C -> C) -> (Base -> C -> C) -> C
TypeRec (CBase BBool) b i l t = b BBool
TypeRec (CBase BInt) b i l t = i BInt
TypeRec (CList x) b i l t = l x (TypeRec x b i l t)
-- These cases should be `t x (TypeRec (CBase x) b i l t)` but that's
-- not structurally recursive, so we just inline the TypeRec call
TypeRec (CTrace BBool) b i l t = t BBool (b BBool)
TypeRec (CTrace BInt) b i l t = t BInt (i BInt)

total
VALUE' : C -> C
VALUE' a = TypeRec a CBase CBase (\_, b => CList b) (\a, _ => CBase a)

total
VALUE_VALUE' : (a: C) -> VALUE a = VALUE' a
VALUE_VALUE' (CBase BBool) = Refl
VALUE_VALUE' (CBase BInt) = Refl
VALUE_VALUE' (CList x) = cong (VALUE_VALUE' x)
VALUE_VALUE' (CTrace BBool) = Refl
VALUE_VALUE' (CTrace BInt) = Refl
