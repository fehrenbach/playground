module Record

-- based on https://github.com/jmars/Records
-- and http://lpaste.net/104020
-- mostly me renaming stuff while trying to understand what's going on.

%access public export
%default total

infix 5 :=

-- jmars says it's just a pair. Can we remove it and actually use a pair, with (:=) = (,)?
data Field : labelType -> Type -> Type where
  (:=) : (label : labelType) -> value -> Field label value

data Record : List (labelType, Type) -> Type where
  Nil  : Record []
  -- can/should we constrain this so we can have every label only once?
  (::) : Field label a -> Record row -> Record ((label, a) :: row)

-- A predicate that states that a label is present in a row with some type
data LabelPresent : labelType -> List (labelType, Type) -> Type -> Type where
  Here  : LabelPresent label ((label, typ) :: _) typ
  There : LabelPresent label row typ -> LabelPresent label (_ :: row) typ

-- jmars's version does not have the label, Edwin's does.
-- We don't need it, since we pattern match on the proof.
-- I suspect we should avoid that if we were interested in good erasure behaviour.
project' : {- (label : labelType) -> -} Record row -> LabelPresent label row typ -> typ
project' {- label -} ((label := value) :: _) Here = value
project' {- label -} (_ :: row) (There x) = project' {- label -} row x

(.) : Record row -> (label : labelType) -> { auto prf : LabelPresent label row typ } -> typ
(.) r label {prf} = project' {- label -} r prf

-- to do, or not: record concatenation, field removal, field update, ...

-- %language ElabReflection

trains : Record {labelType=Int} ?trainsType
trains = [4468 := "Mallard",
          4472 := "Flying Scotsman",
          1    := "Thomas"]
trainsType = proof search -- this should be possible using %runElab

juno : Record {labelType=String} ?movieType
juno = [ "title" := "Juno"
       , "actors" := the (List _) ["Ellen Page", "Michael Cera"] ]
movieType = proof search

test : "Ellen Page" = head (the (List _) ([ "title" := "Juno", "actors" := ["Ellen Page", "Michael Cera"] ] . "actors"))
test = Refl
