module Main where

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Data.Const (Const)
import Data.Identity (Identity(..))
import Data.Newtype (unwrap, wrap)
import Data.Record (get, insert)
import Prelude hiding (Ordering(..))
import Type.Prelude (class IsSymbol, SProxy(..))
import Type.Row (class ListToRow, class RowLacks, class RowToList, Cons, Nil, kind RowList)
import Unsafe.Coerce (unsafeCoerce)

silenceWarning :: SProxy "abc"
silenceWarning = SProxy

-- remove REPR type constructor from row list
class RemoveRepr
      (repr :: Type -> Type)
      (la :: RowList)
      (lb :: RowList)
  | la -> lb
  , lb -> la

instance applyReprNil :: RemoveRepr repr Nil Nil
instance applyReprCons ::
  RemoveRepr repr la lb =>
  RemoveRepr repr (Cons k (repr a) la) (Cons k b lb)

record :: forall a b repr la lb.
  RowToList a la =>
  RemoveRepr repr la lb =>
  ListToRow lb b =>
  Record a -> repr (Record b)
record a = unsafeCoerce a -- TODO implementation

foo :: forall repr. Symantics repr => repr { a :: Int, b :: Int }
foo = record {a: plus (int 2) (int 40), b: int 5 }

-- map row list of As to row list of Bs
class RecordMap
      (tyf :: Type -> Type)
      (la :: RowList)
      (lb :: RowList)
      | la -> lb
      , lb -> la

instance recordMapNil :: RecordMap tyf Nil Nil
instance recordMapCons :: RecordMap tyf la lb => RecordMap tyf (Cons k a la) (Cons k (tyf a) lb)

recordMap :: forall tyf a b as bs las lbs.
             RowToList as las =>
             RecordMap tyf las lbs =>
             ListToRow lbs bs =>
             (String -> a -> b) -> Record as -> Record bs
recordMap f r = unsafeCoerce "TODO"

-- nope, doesn't work. I somehow need to express that the function is
-- sufficiently polymorphic to deal with everything in the input
-- record.
-- abc :: { a :: String, b :: String }
-- abc = recordMap (\l _ -> l) {a: 3, b: true}

abc' :: { a :: Const String Int, b :: Const String Boolean, c :: Const String { abc :: Number } }
abc' = recordMap (\l _ -> l) {a: 3, b: true, c: {abc: 5.5} }

abc :: {a :: String, b :: String, c :: String}
abc = recordUnconst abc'

-- How would I define an easier to use rmap without this Const business?
-- rmap f r = recordUnconst (recordMap f r)
-- foo = rmap (\l _ -> l) {a: 3, b: 5.5}

class RemoveConst
      (la :: RowList)
      (lb :: RowList)
      | la -> lb
      , lb -> la

instance removeConstNil :: RemoveConst Nil Nil
instance removeConstCons :: RemoveConst la lb => RemoveConst (Cons k (Const r i) la) (Cons k r lb)

recordUnconst :: forall as las bs lbs.
  RowToList as las =>
  RemoveConst las lbs =>
  ListToRow lbs bs =>
  Record as -> Record bs
recordUnconst r = unsafeCoerce "TODO"

class Symantics repr where
  int :: Int -> repr Int
  plus :: repr Int -> repr Int -> repr Int
  var :: forall a. a -> repr a
  proj :: forall nm r r' t.
          IsSymbol nm => RowCons nm t r r' =>
          SProxy nm -> repr (Record r') -> repr t
  rnil :: repr (Record ())
  rcons :: forall label t a b.
           IsSymbol label => RowLacks label a => RowCons label t a b =>
           SProxy label -> repr t -> repr (Record a) -> repr (Record b)
  -- record :: forall a. {| a} -> repr (Record a)

instance evaluatorSemantics :: Symantics Identity where
  int x = wrap x
  plus x y = wrap (unwrap x + unwrap y)
  var v = wrap v
  proj nm r = wrap (get nm (unwrap r))
  rnil = wrap {}
  -- can't use unwrap for some reason..
  rcons l (Identity v) (Identity r) = wrap (insert l v r)
  -- record r = wrap r

tttrace :: forall r. Symantics r => r Int
tttrace = plus (int 2) (int 2)

ab :: forall r. Symantics r => r Int
ab = proj (SProxy :: SProxy "a") (rcons (SProxy :: SProxy "b") (int 5)
                                  (rcons (SProxy :: SProxy "a") (plus (int 2) (int 40))
                                   rnil))

value :: forall a. Identity a -> a
value (Identity t) = t


main :: forall e. Eff (console :: CONSOLE | e) Unit
main = do
  log (show (value tttrace))
  log (show (value ab))
  log (show (value (proj (SProxy :: SProxy "a") foo)))
  log (show (value (proj (SProxy :: SProxy "b") foo)))
