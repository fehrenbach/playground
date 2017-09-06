module Main where

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)
import Data.Const (Const)
import Data.Identity (Identity(..))
import Data.Leibniz (type (~), coerceSymm)
import Data.Newtype (unwrap, wrap)
import Data.Record (get, insert)
import Prelude hiding (Ordering(..))
import Type.Prelude (class IsSymbol, SProxy(..))
import Type.Row (class ListToRow, class RowLacks, class RowToList, Cons, Nil, RProxy(..), kind RowList)
import Unsafe.Coerce (unsafeCoerce)

silenceWarning :: SProxy "abc"
silenceWarning = SProxy
ces :: ∀ a b. a ~ b → b → a
ces = coerceSymm
ins :: ∀ r1 r2 l a. IsSymbol l ⇒ RowLacks l r1 ⇒ RowCons l a r1 r2 ⇒ SProxy l → a → Record r1 → Record r2
ins = insert
bar :: forall a b c. RowLacks a b => c
bar = unsafeCoerce "f"


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
  RemoveRepr repr (Cons k (repr a) la) (Cons k a lb)

-- record' :: forall a b repr la lb.
--   RowToList a la =>
--   RemoveRepr repr la lb =>
--   ListToRow lb b =>
--   Record a -> repr (Record b)
-- record' a = unsafeCoerce a -- TODO implementation

-- foo :: forall repr. Symantics repr => repr { a :: Int, b :: Int }
-- foo = record' {a: plus (int 2) (int 40), b: int 5 }

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
  -- rnil :: repr (Record ())
  -- rcons :: forall label t a b.
           -- IsSymbol label => RowLacks label a => RowCons label t a b =>
           -- SProxy label -> repr t -> repr (Record a) -> repr (Record b)
  record :: forall a b la lb.
            RowToList a la =>
            RemoveRepr repr la lb =>
            ListToRow lb b =>
            Record a -> repr (Record b)

instance evaluatorSemantics :: Symantics Identity where
  int x = wrap x
  plus x y = wrap (unwrap x + unwrap y)
  var v = wrap v
  proj nm r = wrap (get nm (unwrap r))
  -- rnil = wrap {}
  -- can't use unwrap for some reason..
  -- rcons l (Identity v) (Identity r) = wrap (insert l v r)
  -- record r = wrap r
  record r = unsafeCoerce r

tttrace :: forall r. Symantics r => r Int
tttrace = plus (int 2) (int 2)

-- ab :: forall r. Symantics r => r Int
-- ab = proj (SProxy :: SProxy "a") (rcons (SProxy :: SProxy "b") (int 5)
                                  -- (rcons (SProxy :: SProxy "a") (plus (int 2) (int 40))
                                   -- rnil))

ab' :: forall r. Symantics r => r Int
ab' = proj (SProxy :: SProxy "b") (record { a: plus (int 2) (int 40)
                                          , b: int 5 })

value :: forall a. Identity a -> a
value (Identity t) = t

-- data Where a = Where a

-- fakeRecord v = { table: "Fake"
               -- , column: "News"
               -- , row: -1
               -- , data: v }

-- instance whereSemantics :: Symantics Where where
--   int x = Where x
--   plus (Where x) (Where y) = Where (x + y)
--   var v = Where v
--   proj nm (Where r) = Where (get nm r)
--   rnil = Where {}

--   rcons :: forall label t a b.
--            IsSymbol label => RowLacks label a => RowCons label t a b =>
--            SProxy label -> Where t -> Where (Record a) -> Where (Record b)
--   rcons l (Where v) (Where r) = Where (insert l (fakeRecord v) r)

-- newtype W a = W { data :: a }

-- class WhereList (la :: RowList) (lb :: RowList) | la -> lb
-- instance whereListNil :: WhereList Nil Nil
-- instance whereListCons ::
--   (Where a b,
--    WhereList la lb) =>
--   WhereList (Cons k a la) (Cons k (W b) lb)

-- class Where a b | a -> b where
--   fake :: a -> b

-- instance whereInt :: Where Int Int where
--   fake = id
-- instance whereString :: Where String String where
--   fake = id
  
-- instance whereRecord ::
--   (RowToList a la,
--    WhereList la lb,
--    ListToRow lb b) =>
--   Where (Record a) (Record b) where
--   fake r = recordMap (\l v -> fakeRecord v) r

-- abc :: forall x y. Where x y => x -> y
-- abc asentuh = ?huh

class RemoveTrace
      (la :: RowList)
      (lb :: RowList)
  | la -> lb
  , lb -> la

instance removeTraceNil :: RemoveTrace Nil Nil
instance removeTraceCons ::
  RemoveTrace la lb =>
  RemoveTrace (Cons k (Trace t) la) (Cons k t lb)

-- data ProjTraceInner a s t b whatever = ProjTraceInner (IsSymbol s =>
--                RowCons s t whatever b =>
--                { t :: a ~ t
--                , name :: SProxy s
--                , record :: Record b })

-- data Test = Test (forall a. Show a => { foo :: a })

-- test :: Test -> String
-- test (Test { foo }) = show foo

-- class RowListHas (f :: Type -> Type) (l :: RowList)

-- instance rowListHasNil :: RowListHas f Nil
-- instance rowListHasCons :: RowListHas f l => RowListHas f (Cons k (f x) l)

data Trace a
  = IntTrace { t :: (a ~ Int)
             , v :: Int }
  | PlusTrace { t :: a ~ Int
              , left :: Trace Int
              , right :: Trace Int }
  | RecordTrace (forall b lb la r.
                 RowToList b lb =>
                 RemoveTrace lb la =>
                 ListToRow la r =>
                 { t :: a ~ Record r
                 , rs :: Record b
                 })
  | ProjTrace (forall s t b whatever.
               IsSymbol s =>
               RowCons s t whatever b =>
               { t :: a ~ t
               , name :: SProxy s
               , record :: Trace (Record b) })

test42 :: Trace Int
test42 = IntTrace { t: id
                  , v: 42 }

test :: Trace { a :: Trace Int }
test = RecordTrace { rs: { a: test42 }
                   , t: ?huh }

-- test = RecordTrace { rs: {a: IntTrace { t: ?bar
                                      -- , v: 42 }
                         -- }
                   -- , t: ?huh }

-- v :: forall a. Trace a -> a
-- v (IntTrace {t, v}) = coerceSymm t v
-- v (PlusTrace {t, left, right}) = coerceSymm t (v left + v right)
-- v (ProjTrace foo) = ?bar
-- v _ = ?todo

main :: forall e. Eff (console :: CONSOLE | e) Unit
main = do
  log (show (value tttrace))
  -- log (show (value ab))
  log (show (value ab'))
  -- log (show (value (proj (SProxy :: SProxy "a") foo)))
  -- log (show (value (proj (SProxy :: SProxy "b") foo)))
