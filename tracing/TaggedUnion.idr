module TaggedUnion

%access public export
%default total

-- Right, this was harder than I'd like, but here we go: variants/tagged unions

data LabelPresent : String -> Type -> List (String, Type) -> Type where
  Here : LabelPresent label typ ((label, typ) :: _)
  There : LabelPresent label typ var -> LabelPresent label typ (_ :: var)

data Variant : List (String, Type) -> Type where
  InV : (label : String) -> typ -> {auto prf : LabelPresent label typ v} -> Variant v

data Elim : String -> Type -> Type -> Type where
  Case : (label : String) -> (a -> b) -> Elim label a b

data Elims : List (String, Type) -> Type -> Type where
  Nil : Elims [] t
  (::) : Elim label typ t -> Elims v t -> Elims ((label, typ) :: v) t

elim : Variant v -> Elims v t -> t
elim {v=[]} (InV _ _ {prf = Here}) [] impossible
elim {v=[]} (InV _ _ {prf = (There _)}) [] impossible
elim {v=((label, typ) :: xs)} (InV label x {prf = Here}) ((Case label f) :: z) = f x
elim (InV label x {prf = There w}) (_ :: z) = elim (InV label x {prf=w}) z

-- Use like: someVal `switch` [Case "a" (\a => stuff), Case "b" (\b => stuff')]
switch : Variant v -> Elims v t -> t
switch = elim

AIntOrBBool : Type
AIntOrBBool = Variant [("a", Int), ("b", Bool)]

l5' : AIntOrBBool
l5' = InV "a" 5 

rTrue' : AIntOrBBool
rTrue' = InV "b" True

print : AIntOrBBool -> String
print v = elim v [Case "a" (\i => "a:int"), Case "b" (\b => "b:bool")]
