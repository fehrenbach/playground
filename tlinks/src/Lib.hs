{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Lib where

import Bound (Var(B,F))
import Bound.Scope.Simple
import qualified Bound.Scope as BS
import Common
import Control.Exception (assert)
import Control.Monad (replicateM, forM_)
import Control.Monad.Morph (lift)
import Data.Void (Void)
import Data.Functor (void)
import Data.List (all, foldl')
import Data.Bifunctor (first, second)
import qualified Debug.Trace as Debug
import GHC.Stack (HasCallStack)
import Expr
import Type (Type, Kind)
import qualified Shredding as S
import qualified Type as T
import qualified Hedgehog as H
import           Hedgehog hiding (Var, assert)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Text.PrettyPrint.ANSI.Leijen (putDoc)

-- the value trace analysis function
value :: Eq a => Expr Type a x
value = Fix (T.Forall T.KType (BS.toScope (T.Arrow
                                           (T.Var (B ()))
                                           (T.App T.valuetf (T.Var (B ())))))) $ toScope $ TLam T.KType $ Typecase (toScope (T.Var (B ())))
        -- Bool
        (Lam (lift T.Bool) (toScope (Var (B ()))))
        -- Int
        (Lam (lift T.Int) (toScope (Var (B ()))))
        -- String
        (Lam (lift T.String) (toScope (Var (B ()))))
        -- List
        (Lam (lift (toScope (T.List (T.Var (B ())))))
          (toScope (For (Var (B ()))
                     (toScope (Singleton ((:$) ((:§) (Var (F (F (B ())))) (toScope (toScope (T.Var (B ()))))) (Var (B ()))))))))
        -- Record
        (Lam (toScope (toScope (T.Record (T.Var (B ())))))
          (toScope (Rmap (Var (F (B ()))) (toScope (toScope (T.Record (T.Var (B ()))))) (Var (B ())))))
        -- Trace
        (Lam (toScope (toScope (T.Trace (T.Var (B ())))))
         (toScope (Tracecase (Var (B ()))
                   -- Lit
                   (toScope (Var (B ())))
                   -- If
                   (toScope ((:$) ((:§) (Var (F (F (B ())))) (toScope (toScope (T.App T.tracetf (T.Var (B ()))))))
                              (Proj "out" (Var (B ())))))
                   -- For
                   (toScope ((:$) ((:§) (Var (F (F (B ())))) (toScope (toScope (toScope (T.App T.tracetf (T.Var (F (B ()))))))))
                             (Proj "out" (Var (B ())))))
                   -- Row
                   (toScope (Proj "data" (Var (B ()))))
                   -- OpEq
                   (toScope (Eq (toScope (toScope (toScope (T.Var (B ())))))
                             ((:$) ((:§) (Var (F (F (B ())))) (toScope (toScope (toScope (T.Var (B ()))))))
                               (Proj "left" (Var (B ()))))
                             ((:$) ((:§) (Var (F (F (B ())))) (toScope (toScope (toScope (T.Var (B ()))))))
                               (Proj "right" (Var (B ()))))))
                    -- OpAnd
                    (toScope (And
                              (Var (F (F (B ()))) :§ toScope (toScope (T.Trace T.Bool)) :$ Proj "left" (Var (B ())))
                              (Var (F (F (B ()))) :§ toScope (toScope (T.Trace T.Bool)) :$ Proj "right" (Var (B ())))))
                    -- OpGEq
                    (toScope (GEq
                              (Var (F (F (B ()))) :§ toScope (toScope (T.Trace T.Int)) :$ Proj "left" (Var (B ())))
                              (Var (F (F (B ()))) :§ toScope (toScope (T.Trace T.Int)) :$ Proj "right" (Var (B ())))))
                   )))

wherep :: Eq a => Expr Type a x
wherep = Fix (T.Forall T.KType (BS.toScope (T.Arrow (T.Var (B ())) (T.App T.wheretf (T.Var (B ())))))) $ toScope $ TLam T.KType $ Typecase (toScope (T.Var (B ())))
  -- Bool
  (Lam (lift T.Bool) (toScope (Record [("data", Var (B ())), ("table", string "facts"), ("column", string "alternative"), ("row", int (-1))])))
  -- Int
  (Lam (lift T.Int) (toScope (Record [("data", Var (B ())), ("table", string "facts"), ("column", string "alternative"), ("row", int (-1))])))
  -- String
  (Lam (lift T.String) (toScope (Record [("data", Var (B ())), ("table", string "facts"), ("column", string "alternative"), ("row", int (-1))])))
  -- List
  (Lam (lift (toScope (T.List (T.Var (B ()))))) 
   (toScope (For (Var (B ())) (toScope (Singleton (Var (F (F (B ()))) :§ toScope (toScope (T.Var (B ()))) :$ Var (B ())))))))
  -- Record
  (Lam (toScope (toScope (T.Record (T.Var (B ())))))
    (toScope (Rmap (Var (F (B ()))) (toScope (toScope (T.Record (T.Var (B ()))))) (Var (B ())))))
  -- Trace
  (Lam (toScope (toScope (T.Trace (T.Var (B ())))))
    (toScope (Tracecase (Var (B ()))
               -- Lit
               (toScope (Record [("data", Var (B ())), ("table", string "facts"), ("column", string "alternative"), ("row", int (-1))]))
               -- If
               (toScope (Var (F (F (B ()))) :§ toScope (toScope (T.Trace (T.Var (B ())))) :$ Proj "out" (Var (B ()))))
               -- For
               (toScope (Var (F (F (B ()))) :§ toScope (toScope (toScope (T.Trace (T.Var (F (B ())))))) :$ Proj "out" (Var (B ()))))
               -- Row
               (toScope (Var (B ())))
               -- OpEq
               (toScope (Record [ ("data", Eq (toScope (toScope (toScope (T.Var (B ())))))
                                           (liftCE (liftCE (liftCE value)) :§ toScope (toScope (toScope (T.App T.tracetf (T.Var (B ()))))) :$ (Proj "left" (Var (B ()))))
                                           (liftCE (liftCE (liftCE value)) :§ toScope (toScope (toScope (T.App T.tracetf (T.Var (B ()))))) :$ (Proj "right" (Var (B ())))))
                                , ("table", string "facts"), ("column", string "alternative"), ("row", int (-1))]))
             -- OpAnd
             (toScope (Record [ ("data",
                                 And
                                  ((liftCE (liftCE value)) :§ toScope (toScope (T.Trace T.Bool)) :$ Proj "left" (Var (B ())))
                                  ((liftCE (liftCE value)) :§ toScope (toScope (T.Trace T.Bool)) :$ Proj "right" (Var (B ()))))
                              , ("table", string "facts"), ("column", string "alternative"), ("row", int (-1))]))
             -- OpGEq
             (toScope (Record [ ("data",
                                 GEq
                                  ((liftCE (liftCE value)) :§ toScope (toScope (T.Trace T.Int)) :$ Proj "left" (Var (B ())))
                                  ((liftCE (liftCE value)) :§ toScope (toScope (T.Trace T.Int)) :$ Proj "right" (Var (B ()))))
                              , ("table", string "facts"), ("column", string "alternative"), ("row", int (-1))]))
             )))

linnotation :: Eq a => Expr Type a x
linnotation = Fix (T.Forall T.KType (BS.toScope (T.Arrow (T.App T.tracetf (T.Var (B ())))
                                                  (T.List (T.record [("table", T.String), ("row", T.Int)]))))) $ toScope $ TLam T.KType $ Typecase (toScope (T.Var (B ())))
              (Lam (lift T.Bool) (toScope (Empty (lift (T.record [("table", T.String), ("row", T.Int)])))))
              (Lam (lift T.Int) (toScope (Empty (lift (T.record [("table", T.String), ("row", T.Int)])))))
              (Lam (lift T.String) (toScope (Empty (lift (T.record [("table", T.String), ("row", T.Int)])))))
              (Lam (lift (toScope (T.List (T.Var (B ())))))
               (toScope (For (Var (B ()))
                          (toScope (Var (F (F (B ()))) :§ (toScope . toScope) (T.Var (B ())) :$ Var (B ()))))))
              (Lam (lift (toScope (T.Record (T.Var (B ())))))
               (toScope (Rfold
                         (TLam T.KType (Lam (lift (lift (lift (T.List (T.record [("table", T.String), ("row", T.Int)])))))
                                         (toScope (Lam (toScope (toScope (toScope (T.Var (B ())))))
                                                    (toScope (Concat [ Var (F (B ()))
                                                                     , Var (F (F (F (B ())))) :§ toScope (toScope (toScope (T.Var (B ())))) :$ Var (B ()) ]))))))
                         (Empty (lift (lift (T.record [("table", T.String), ("row", T.Int)]))))
                         (Var (B ()))
                         (toScope (toScope (T.Record (T.Var (B ()))))))))
              (Lam (toScope (toScope (T.App T.tracetf (T.Var (B ())))))
               (toScope (Tracecase (Var (B ()))
                         (toScope (Empty ((lift . lift) (T.record [("table", T.String), ("row", T.Int)]))))
                         -- this is without the annotations from .cond
                         (toScope (Var (F (F (B ()))) :§ toScope (toScope (T.App T.tracetf (T.Var (B ())))) :$ Proj "out" (Var (B ()))))
                         (toScope
                           (Concat [ Var (F (F (B ()))) :§ toScope (toScope (toScope (T.App T.tracetf (T.Var (B ()))))) :$ Proj "in" (Var (B ()))
                                   , Var (F (F (B ()))) :§ toScope (toScope (toScope (T.App T.tracetf (T.Var (F (B ())))))) :$ Proj "out" (Var (B ()))]))
                          -- Row
                         (toScope (Singleton (Record [ ("table", Proj "table" (Var (B ())))
                                                     , ("row", Proj "row" (Var (B ())))])))
                          -- Op==
                         (toScope
                           (Concat [ Var (F (F (B ()))) :§ toScope (toScope (toScope (T.App T.tracetf (T.Var (B ()))))) :$ Proj "left" (Var (B ()))
                                   , Var (F (F (B ()))) :§ toScope (toScope (toScope (T.App T.tracetf (T.Var (B ()))))) :$ Proj "right" (Var (B ()))]))
                          -- Op&&
                          (toScope
                            (Concat [ Var (F (F (B ())))
                                      :§ toScope (toScope (T.Trace T.Bool))
                                      :$ Proj "left" (Var (B ()))
                                    , Var (F (F (B ())))
                                      :§ toScope (toScope (T.Trace T.Bool))
                                      :$ Proj "right" (Var (B ()))]))
                          -- Op>=
                          (toScope
                            (Concat [ Var (F (F (B ())))
                                      :§ toScope (toScope (T.Trace T.Bool))
                                      :$ Proj "left" (Var (B ()))
                                    , Var (F (F (B ())))
                                      :§ toScope (toScope (T.Trace T.Bool))
                                      :$ Proj "right" (Var (B ()))]))
                           -- (Concat [ Var (F (F (B ()))) :§ toScope (toScope (toScope (T.Trace T.Bool))) :$ Proj "left" (Var (B ()))
                           --         , Var (F (F (B ()))) :§ toScope (toScope (toScope (T.Trace T.Bool))) :$ Proj "right" (Var (B ()))]))
                        )))

lineage :: Eq a => Expr Type a x
lineage = Fix (T.Forall T.KType (BS.toScope (T.Arrow (T.App T.tracetf (T.Var (B ()))) (T.App T.lineagetf (T.Var (B ())))))) $ toScope $ TLam T.KType $ Typecase (toScope (T.Var (B ())))
  (Lam (lift T.Bool) (toScope (Var (B ()))))
  (Lam (lift T.Int) (toScope (Var (B ()))))
  (Lam (lift T.String) (toScope (Var (B ()))))
  (Lam (toScope (toScope (T.List (T.Var (B ())))))
    (toScope (For (Var (B ()))
              (toScope (Singleton (Record
                                   [("data", Var (F (F (B ()))) :§ toScope (toScope (T.Var (B ()))) :$ Var (B ()))
                                   ,("lineage", liftCE (liftCE linnotation) :§ toScope (toScope (T.Var (B ()))) :$ Var (B ()))]))))))
  (Lam (toScope (toScope (T.Record (T.Var (B ())))))
    (toScope (Rmap (Var (F (B ()))) (toScope (toScope (T.Record (T.Var (B ()))))) (Var (B ())))))
  (Lam (toScope (toScope (T.App T.tracetf (T.Var (B ())))))
   (toScope (liftCE (liftCE value) :§ toScope (toScope (T.App T.tracetf (T.Var (B ())))) :$ Var (B ()))))

unroll :: Eq a => Monad c => Int -> Expr c a x -> Expr c a x
unroll 0 (Fix _ _) = Const Bottom
unroll n (Fix t b) = unroll (n-1) (instantiate1 (Fix t b) b)
unroll _ (Const c) = Const c
unroll _ (Var x) = Var x
unroll n (If c t e) = If (unroll n c) (unroll n t) (unroll n e)
unroll n (Lam t b) = Lam t (hoistScope (unroll n) b)
unroll n ((:$) a b) = (:$) (unroll n a) (unroll n b)
unroll n (TLam k b) = TLam k (unroll n b)
unroll n ((:§) e c) = (:§) (unroll n e) c
unroll _ (Empty t) = Empty t
unroll n (Singleton e) = Singleton (unroll n e)
unroll n (Concat l) = Concat (unroll n <$> l)
unroll n (For i o) = For (unroll n i) (hoistScope (unroll n) o)
unroll n (Record l) = Record (mapSnd (unroll n) l)
unroll n (Proj l e) = Proj l (unroll n e)
unroll _ (Table name t) = Table name t
unroll n (Rmap a t b) = Rmap (unroll n a) t (unroll n b)
unroll n (Rfold a b c t) = Rfold (unroll n a) (unroll n b) (unroll n c) t
unroll n (Eq t l r) = Eq t (unroll n l) (unroll n r)
unroll n (And l r) = And (unroll n l) (unroll n r)
unroll n (GEq l r) = GEq (unroll n l) (unroll n r)
unroll n (Typecase c b i s l r t) = Typecase c (unroll n b) (unroll n i) (unroll n s) (unroll n l) (unroll n r) (unroll n t)
unroll n (Tracecase x l i f r oe oa ogeq) = Tracecase
  (unroll n x)
  (hoistScope (unroll n) l)
  (hoistScope (unroll n) i)
  (hoistScope (unroll n) f)
  (hoistScope (unroll n) r)
  (hoistScope (unroll n) oe)
  (hoistScope (unroll n) oa)
  (hoistScope (unroll n) ogeq)
unroll n (Trace tr e) = Trace tr (unroll n e)
unroll n (e ::: t) = (unroll n e) ::: t

one :: Show x => Show a => Eq a => Expr Type a x -> Expr Type a x
one (Const c) = Const c
one (Var v) = Var v
one (If (Const (Bool True)) t _) = t
one (If (Const (Bool False)) _ e) = e
one (If c t e) = If (one c) (one t) (one e)
one ((:$) (Lam _ b) a) = instantiate1 a b
one ((:$) a b) = (:$) (one a) b
-- one (E(:$) a b) = E(:$) (one a) (one b) -- one b is not necessary, but helps finding bugs
-- one (Lam t b) = Lam t (hoistScope one b) -- for debugging only
one l@Lam{} = l -- do not normalize under lambda
one (Fix _ _) = error "Unexpected fix"
one (TLam _ _) = error "TODO Lambda"
one ((:§) (TLam _ b) c) = eInstantiateC1 c b
one ((:§) a c) = (:§) (one a) c
one (Table n t) = Table n t
one (Empty t) = Empty t
one (Singleton e) = Singleton (one e)
one (Concat []) = error "empty Concat"
one (Concat l) = case foldr f ([], Nothing) (map one l) of
  ([], Just t) -> Empty t
  ([x], _) -> x
  (xs, _) -> Concat xs
  where -- accumulate non-emptys, and record type of empty
    f (Empty t) (xs, _) = (xs, Just t)
    f x (xs, mt) = (x:xs, mt)
one f@(For (Empty _) _) = Empty (elementType (typeof f))
  where elementType (T.List et) = et
        elementType _ = error "not a list type"
one (For (Singleton e) o) = instantiate1 e o
one (For (Concat ls) o) = Concat (map (\l -> For l o) ls)
one (For (If c t e) o) = If c (For t o) (For e o)
-- for (x <- for (y <- L) M) N ~> for (y <- L) (for (x <- M) N)
-- This circumvents the safety implied by the Scope scope safety, but
-- should be correct. Variables in L stay unchanged. y is visible in
-- M, bound by the preceding for. The nesting looks different in
-- source code, but the binding structure is the same. On the left
-- side, x is visible in N, bound by the outer for. On the right side,
-- x is visible in N, bound by the outer for, so that stays the same.
-- On the right side, y is visible in N, but not used. However, all
-- other free variables need to move up one binder to account for y.
one (For (For l (Scope m)) n) =
  For l (Scope (For m (F <$> n)))
-- no, no, need proper elim frames
-- one (EFor t (EVar x) o) = EFor t (EVar x) (hoistScope one o) -- for debugging only

-- without eta expansion of tables:
one (For (Table n tt) o) = For (Table n tt) (hoistScope one o)
-- -- with eta expansion of tables:
-- one (For t (Table n tt@(TT (CRecord row))) o) = For t (Table n tt) etaO --(hoistScope one o)
  -- where
    -- etaO :: Scope () (Expr Type a) x
    -- etaO = Scope (splat (pure . F) (const (ERecord (map (\(l, _) -> (l, EProj l tt (EVar (B ())))) (rowToList row)))) o)
one (For i o) = For (one i) o --(hoistScope one o)
one (Record fs) = Record (mapSnd one fs)
one (Rfold f a r (T.Record row)) =
  foldl' (\acc (l, t) ->
            f :§ t :$ acc :$ Proj l r
         ) a (T.rowToList row)
one (Rmap f (T.Record row) r) = Record
  (map (\(l,t) -> (l, f :§ t :$ Proj l r))
    (T.rowToList row))
one (Rmap _ _ _) = error "TODO need to normalize type (and switch to constructor, not type to begin with, I think"
one (Proj l (Record fs)) = case lookup l fs of
  Nothing -> error $ "label '" ++ l ++ "' not found in record"
  Just e -> e
one (Proj l (If c t e)) = If c (Proj l t) (Proj l e)
one (Proj l e) = Proj l (one e)
-- one (EEq _ l r) | l == r = ETrue --
one (Eq _ Empty{} Empty{}) = Const (Bool True)
one (Eq _ (Const l) (Const r)) = Const (Bool (l == r))
one (Eq t l r) = Eq t (one l) (one r)
one (And _ (Const (Bool False))) = Const (Bool False)
one (And (Const (Bool False)) _) = Const (Bool False)
one (And (Const (Bool True)) r) = r
one (And l (Const (Bool True))) = l
one (And l r) = And (one l) (one r) 
one (GEq l r) = GEq (one l) (one r)
one (Typecase c b i s l r t) = case c of
  T.Bool -> b; T.Int -> i; T.String -> s;
  T.List c' -> eInstantiateC1 c' l
  T.Record c' -> eInstantiateC1 c' r
  T.Trace c' -> eInstantiateC1 c' t
  _ -> Typecase (T.norm c) b i s l r t
one (Tracecase (If c t e) l i f r oe oa ogeq) = If c (Tracecase t l i f r oe oa ogeq) (Tracecase e l i f r oe oa ogeq)
one (Tracecase x l i f r oe oa ogeq) = case x of
  -- Record _ -> error "Record in tracecase. There's a type error somewhere"
  Trace tr t -> instantiate1 t (case tr of
                                   TrLit -> l; TrIf -> i; TrRow -> r; TrAnd -> oa; TrGEq -> ogeq;
                                   TrFor c -> hoistScope (eInstantiateC1 c) f
                                   TrEq c -> hoistScope (eInstantiateC1 c) oe)
  x' -> Tracecase (one x') l i f r oe oa ogeq
one (Trace tr e) = Trace tr (one e)
one (e ::: t) = one e ::: t

tid :: Eq a => Monad c => Scope () (Expr c a) x
tid = toScope (Var (B ()))

trace :: HasCallStack => Show x => Eq a => Expr Type a x -> Expr Type a x
trace (Var x) = error "Unannotated variables shouldn't happen, right?" -- Var x
trace (Var x ::: t) = Var x -- ::: t
trace (e ::: t) = trace e
trace (Const c) = Trace TrLit (Const c)
trace (If c t e) =
  If (value :§ T.Trace T.Bool :$ trace c)
  ((distTRACE (toScope (Trace TrIf (Record [("cond", F <$> trace c), ("out", Var (B ()))]))) (typeof t)) :$ trace t)
  ((distTRACE (toScope (Trace TrIf (Record [("cond", F <$> trace c), ("out", Var (B ()))]))) (typeof e)) :$ trace e)
trace (Empty c) = Empty (T.App T.tracetf c)
trace (Singleton e) = Singleton (trace e)
trace (Concat l) = Concat (trace <$> l)
trace (For ie o) =
  let (T.List it) = T.norm (typeof ie) in
  For (trace ie)
      (toScope (distTRACE (toScope (Trace (TrFor (T.App T.tracetf it))
                                    (Record [("in", Var (F (B ()))), ("out", Var (B ()))])))
                 (typeof (instantiate1 (Const Bottom ::: it) o))
                 :$ trace (fromScope o)))
trace (Record fields) = Record (second trace <$> fields)
trace (Proj l r) = Proj l (trace r)
trace (Table n (T.Record row)) = For (Table n (T.Record row))
  (toScope (Singleton (Record (map (\(l,_) -> (l, tblTrace l)) (T.rowToList row)))))
  where tblTrace l = Trace TrRow (Record [("table", Const (String n)),
                                          ("column", Const (String l)),
                                          ("row", Proj "oid" (Var (B ()))),
                                          ("data", Proj l (Var (B ())))])
trace (Table _ _) = error "weird table type"
trace (Eq t l r) = Trace (TrEq (T.App T.tracetf t)) (Record [("left", trace l), ("right", trace r)])
trace (And l r) = Trace TrAnd (Record [("left", trace l), ("right", trace r)])
trace (GEq l r) = Trace TrGEq (Record [("left", trace l), ("right", trace r)])
trace Lam{} = error "Found lambda --- argument to trace must be normalized and of query type!"
trace (_ :$ _) = error "Found application --- argument to trace must be normalized and of query type!"
trace (_ :§ _) = error "Found type application --- argument to trace must be normalized and of query type!"
trace Fix{} = error "can't trace fix"
trace TLam{} = error "Found TLam"
trace Rmap{} = error "rmap"
trace Rfold{} = error "rfold"
trace Typecase{} = error "typecase"
trace Tracecase{} = error "tracecase"
trace Trace{} = error "trace"

{-
-- Do I need to do if-hoisting as a separate normalization procedure
-- after beta-normalization and stuff or could I add the if-hoisting
-- rules to my `one` function?

-- Huh, the papers only describe primitive functions (equality and the
-- like) on base types. Equality is easy enough to extend to closed
-- records, you can even do it in the object language with recordfold.
-- I wonder what Links does for open records, lists, and tables.

-- I might want to define the language of query normal forms
-- separately, because it kind of calls for multiple generators and
-- n-ary concatenation. Or maybe I should generalize the respective
-- Expr constructors? The other question is how to deal with variables
-- and scopes. The Table case introduces a fresh variable, but then
-- immediately goes to the calB Singleton case, so I could inline that
-- to avoid having to conjure up a free variable from thin air.

cal o (Proj l x) | T.isBaseType o = Proj l x
cal (T.Record row) m = Record (map (\(l, t) -> (l, calF t l m)) (T.rowToList row))
cal (T.List a) = _ (calB a [] true)

calB a g l (Singleton m) = [ _nestedFors ]
-- I think t is always a Table here, so "generators" are pairs of a
-- table and a variable (name) that refers to it. I'm sure this is
-- expressible with bound somehow.
calB a g l (For _ t m) = calB a (g ++ [t]) l m
calB a g l (Table n ty) = calB (Singleton _x) a (g ++ [t]) l -- fresh x?!
calB a g l (Empty _) = []
calB a g l (Concat m n) = calB a g l m ++ calB a g l n
calB a g l (If l' m n) = calB a g (_and l l') m ++ calB a g (_and l (_not l')) n

calF a l x@(Var _) = cal a (Proj l x)
calF a l (Record fields) = case lookup l fields of
  Just m -> cal a m

-- Something like this?
data Query x
  = QVar x
  | QConst Const
  -- in a query we only ever project variables, so QProj Label x?
  -- what about nested records? I guess they are not in the normal form,
  -- but only constructed as a result?
  | QProj Label (Query x)
  | QUOp (Query x) -- NOT, EXISTS
  | QBOp (Query x) (Query x) -- + - = < AND ...
  | QFor [String]            --   FROM clause/table names
         (Scope Int Query x) --  WHERE clause
         (Scope Int Query x) -- SELECT clause/body
  | QUnionAll [Query x]
-}

-- TODO make this idempotent
-- | Annotate bound variables with the types recorded in their binders
annVars :: Eq a => Expr Type a x -> Expr Type a x
annVars (Const c) = Const c
annVars (a :$ b) = annVars a :$ annVars b
annVars (Lam t b) = Lam t (toScope (annVars (fromScope b >>= \case
                                                B () -> Var (B ()) ::: t
                                                F x -> Var (F x))))
annVars (For i o) =
  let T.List t = T.norm (typeof i) in
    For (annVars i) (toScope (annVars (fromScope o >>= \case
                                          B () -> Var (B ()) ::: t
                                          F x -> Var (F x))))
annVars (Empty c) = Empty c
annVars (Singleton e) = Singleton (annVars e)
annVars (Concat l) = Concat (map annVars l)
annVars (If c t e) = If (annVars c) (annVars t) (annVars e)
annVars e@(Var _ ::: t) = e
annVars (Var _) = error "Variables should be annotated, is this free? Free variable handling needs thinking about and implementing."
annVars (e ::: t) = annVars e ::: t
annVars (Record l) = Record (second annVars <$> l)
annVars (Proj l e) = Proj l (annVars e)
annVars (Eq t l r) = Eq t (annVars l) (annVars r)
annVars (And l r) = And (annVars l) (annVars r)
annVars (GEq l r) = GEq (annVars l) (annVars r)
annVars (Table n t) = Table n t

-- Calls dist, but applies the TRACE type function to the type argument first
distTRACE k t = dist k (T.norm (T.App T.tracetf t))

dist :: forall a x. Scope () (Expr Type a) x -> Type a -> Expr Type a x
-- dist k T.Bool = Lam T.Bool k -- these shouldn't happen, right?
-- dist k T.Int = Lam T.Int k
-- dist k T.String = Lam T.String k
dist k (T.List t) = Lam (T.List t) (toScope (For (Var (B ())) (toScope (Singleton ((F . F <$> dist k t) :$ (Var (B ())))))))
dist k (T.Record row) = Lam (T.Record row) (toScope (Record (map field (T.rowToList row))))
  where
    field :: (Label, Type a) -> (Label, Expr Type a (Var () x))
    field (l, t) = (l, (F <$> dist k t) :$ (Proj l (Var (B ()))))
dist k (T.Trace t) = Lam (T.Trace t) k

-- Ugh. I might need an actual typechecker...
typeof :: HasCallStack => Eq a => Expr Type a x -> Type a
typeof (Var x) = error $ "unannotated var "
typeof (Const Bottom) = error "bottom"
typeof (Const (Bool _)) = T.Bool
typeof (Const (Int _)) = T.Int
typeof (Const (String _)) = T.String
typeof (Const Bottom ::: t) = t
typeof (Var _ ::: t) = t
typeof (e ::: t) = assert (typeof e == t) t
typeof (Record fs) = T.Record (rowType fs)
  where rowType [] = T.RowNil
        rowType ((l,e):es) = T.RowCons l (typeof e) (rowType es)
typeof (Singleton e) = T.List (typeof e)
typeof (Proj l e) = case typeof e of
  T.Record row -> case lookup l (T.rowToList row) of
    Nothing -> error "Label not found in record"
    Just t -> t
  _ -> error "Not a record type in projection"
typeof (If c t e) =
  -- assert (typeof c == T.Bool) $
  -- assert (typeof t == typeof e) $
  typeof t
typeof (Empty c) = T.List c
typeof (Concat []) = error "empty concat"
typeof (Concat (l:_)) =
  -- assert (typeof l == typeof r) $
  typeof l
typeof (f :$ a) = case typeof f of
  T.Arrow ta tb -> {- assert (ta == typeof a) $ -} tb
  _ -> error "not a function type"
typeof (Lam a b)  = T.Arrow a (typeof (instantiate1 (Const Bottom ::: a) b))
typeof (Fix t b) = typeof (instantiate1 (Const Bottom ::: t) b)
typeof (TLam k b) =
  let t = typeof (eInstantiateC1 (T.Var undefined) b)
  in T.Forall k (lift t)
typeof ((TLam k b) :§ t) = typeof (eInstantiateC1 t b)
 -- this is not right, should check function to T.Forall, like :$
typeof (f :§ t) = case T.norm (typeof f) of
  T.Lam k b -> error "type lam"
  T.Forall k b -> BS.instantiate1 t b
typeof (Trace TrLit c) = T.Trace (typeof c)
typeof (Trace TrIf i) = typeof (Proj "out" i)
typeof (Trace (TrFor _) i) = typeof (Proj "out" i)
typeof (Trace TrRow r) = T.Trace (typeof (Proj "data" r))
typeof (Trace (TrEq _) r) = T.Trace T.Bool
typeof (Trace TrAnd r) = T.Trace T.Bool
typeof (Trace TrGEq r) = T.Trace T.Bool
typeof (For i o) =
  let T.List t = T.norm (typeof i) in
  typeof (instantiate1 (Const Bottom ::: t) o)
typeof (Table _ (T.Record row)) =
  assert (all (T.isBaseType . snd) (T.rowToList row)) $
  T.List (T.Record row)
typeof (Table _ _) = error "nonrecord table type"
typeof (Rmap _ _ _) = error "todo"
typeof (Eq _ _ _) = T.Bool
typeof (And _ _) = T.Bool
typeof (GEq _ _) = T.Bool
typeof (Typecase x b i s l r t) = case T.norm x of
  T.Bool -> typeof b
  T.Int -> typeof i
  T.String -> typeof s
  T.List et -> typeof (eInstantiateC1 et l)
  T.Record row -> typeof (eInstantiateC1 row r)
  T.Trace et -> typeof (eInstantiateC1 et t)
  T.Var _ -> error "uh, dunno"
typeof Tracecase{} = error "tracecase"

isOneNF (Const Bottom) = False
isOneNF (Var x) = x
isOneNF (Const _) = True
isOneNF (Eq _ l r) = isOneNF l && isOneNF r
isOneNF (And l r) = isOneNF l && isOneNF r
isOneNF (GEq l r) = isOneNF l && isOneNF r
isOneNF (Empty _) = True
isOneNF (Singleton e) = isOneNF e
isOneNF (Concat l) = all (\case Empty{} -> False; x -> isOneNF x) l
isOneNF (Record fields) = all (isOneNF . snd) fields
isOneNF (Proj _ r) = isOneNF r
isOneNF (_ :$ _) = False
isOneNF (_ :§ _) = False
isOneNF (For Table{} o) = isOneNF $ instantiate1 (Var True) o
-- we kind of want to check that the condition's truth value is not statically known and that the branches are not equivalent, but that's not even implemented in normalization yet...
isOneNF (If c t e) = isOneNF c && isOneNF t && isOneNF e

putE :: Expr Type String String -> IO ()
putE e = do
  putDoc $ prettyExpr (evars, tvars) False e
  putStrLn ""

putC :: Type String -> IO ()
putC c = do
  putDoc $ T.prettyType tvars False c
  putStrLn ""

showTraced :: Expr Type String String -> IO ()
showTraced e = do
  putStrLn "===================="
  putE e
  putStrLn "-------trace---->"
  putE $
    (!! 145) . iterate one $ unroll 3 $
    trace e

true, false :: Expr c a x
true = Const (Bool True)
false = Const (Bool False)

int :: Int -> Expr c a x
int = Const . Int
string :: String -> Expr c a x
string = Const . String

genIf :: Show x => Show a => Eq a => [(x, Type a)] -> Type a -> Gen (Expr Type a x)
genIf env ty = do
  c <- genTypedExpr env T.Bool
  Gen.subtermM2
    (genTypedExpr env ty)
    (genTypedExpr env ty)
    (\t e -> pure (If c t e))

genFor :: Eq a => Show x => Show a => [(x, Type a)] -> Type a -> Gen (Expr Type a x)
genFor env et = do
  t <- T.genType
  ie <- genTypedExpr env (T.List t)
  oe <- genTypedExpr ((B (), t):(first F <$> env)) (T.List et)
  pure (For ie (toScope oe))

boundVars :: HasCallStack => Eq a => Show a => Show x =>
  [(x, Type a)] -> Type a -> [ Gen (Expr Type a x) ]
boundVars env ty = [ pure (Var x) | (x,t) <- env, t == ty ]

genProj :: (Show a, Show x, Eq a) =>
  [(x, Type a)] -> Type a -> Gen (Expr Type a x)
genProj env ty = do
  (l:ls) <- T.genDistinctLabels
  row <- T.genRowFromLabels ls
  r <- genTypedExpr env (T.Record (T.RowCons l ty row))
  pure (Proj l r)

-- TODO this *very* rarely produces terms that use bound variables
-- (and never free variables, but that's good).
genTypedExpr :: HasCallStack => Eq a => Show x => Show a =>
  [(x, Type a)] -> Type a -> Gen (Expr Type a x)
genTypedExpr env ty = Gen.sized $ \size ->
  -- this is like Gen.recursive, but I didn't get how to do that with Gen.frequency
  if size <= 1
  then Gen.frequency base
  else Gen.frequency (base ++ map (second Gen.small) recu)
  where
    -- If there is a variable we could use, we should often use it
    base = map (1,) genBase ++ map (100,) (boundVars env ty)
    -- Use type-specific generators (genRec) more often than polymorphic generators (if, proj,..)
    recu = map (1,) [ genIf env ty, genProj env ty ] ++ map (5,) genRec

    genBase = case ty of
      T.Bool -> [ pure true, pure false ]
      T.Int -> [ Gen.int (Range.constant 0 42) >>= (pure . int) ]
      T.String -> [ Gen.string (Range.constant 0 10) (Gen.unicode) >>= (pure . string) ]
      (T.List (T.Record row))
        | all (T.isBaseType . snd) (T.rowToList row) ->
          [ pure (Empty (T.Record row)),
            do name <- T.genLabel
               pure (Table name (T.Record row)) ]
      (T.List et) -> [ pure (Empty et) ]
      (T.Record row) -> [
        do
          fields <- traverse (\(l, t) ->
                                 genTypedExpr env t >>= pure . (l,))
                    (T.rowToList row)
          pure (Record fields)
        ]

    genRec = case ty of
      T.Bool -> [ do t <- T.genType
                     l <- genTypedExpr env t
                     r <- genTypedExpr env t
                     pure (Eq t l r)
                , do l <- genTypedExpr env T.Bool
                     r <- genTypedExpr env T.Bool
                     pure (And l r)
                , do l <- genTypedExpr env T.Int
                     r <- genTypedExpr env T.Int
                     pure (GEq l r)
                ]
      T.Int -> []
      T.String -> []
      (T.List et) ->
        [ genTypedExpr env et >>= pure . Singleton
        , do n <- Gen.int (Range.exponential 2 1000)
             subterms <- replicateM n (genTypedExpr env ty)
             pure (Concat subterms)
        , genFor env et ]
      (T.Record _) -> []

prop_norm_preserve :: Property
prop_norm_preserve =
  property $ do
    t :: Type String <- forAll $ T.genType
    e :: Expr Type String String <- forAll $ genTypedExpr [] t
    n <- forAll $ Gen.int (Range.linear 0 100)
    norm <- eval $ (!! n) . iterate one $ e
    typeof norm === t

prop_genTypedExpr_typeof :: HasCallStack => Property
prop_genTypedExpr_typeof =
  property $ do
    t <- forAll $ T.genType
    e :: Expr Type String String <- forAll $ genTypedExpr [] t
    te <- eval (typeof e)
    te === t

-- This fails when the query expression uses variables, because they
-- are not type-annotated.
prop_trace_type :: Property
prop_trace_type = property $ do
  t <- forAll $ T.genType
  e :: Expr Type String String <- forAll $ genTypedExpr [] t
  tre <- eval $ (!! 100) . iterate one $ unroll 5 $ trace . annVars $ e
  tretype <- eval (T.norm (typeof tre))
  normt <- eval (T.norm (T.App T.tracetf t))
  tretype === normt

prop_norm_onenf :: Property
prop_norm_onenf = property $ do
  t <- forAll $ T.genType
  e :: Expr Type String String <- forAll $ genTypedExpr [] t
  e' <- eval $ (!! 400) . iterate one $ unroll 20 (value :§ (T.App T.tracetf t) :$ trace (annVars e))
  -- Show-ing unrolled terms >~5 takes too much memory...
  -- Fortunately, it's all lazy and we want to see a prefix anyway!
  -- footnote (take 10000 (show e'))
  H.assert (isOneNF (const True <$> e'))

-- prop_trace_value_type :: Property
-- prop_trace_value_type = property $ do
  -- t <- forAll $ T.genType
  -- e :: Expr Type String String <- forAll $ genTypedExpr [] t
  -- val <- eval $ (!! 1000) . iterate one $ unroll 20 (value :§ (T.App T.tracetf t) :$ trace e)
  -- footnoteShow val
  -- typeof val === t

prop_lineagetf_tracetf :: Property
prop_lineagetf_tracetf = property $ do
  t :: Type Void <- forAll $ T.genType
  T.norm (T.App T.lineagetf (T.App T.tracetf t)) === T.norm (T.App T.lineagetf t)

prop_tracetf_idempotent :: Property
prop_tracetf_idempotent = property $ do
  t :: Type Void <- forAll $ T.genType
  T.norm (T.App T.tracetf (T.App T.tracetf t)) === T.norm (T.App T.tracetf t)

tests :: IO Bool
tests =
  checkParallel $ Group "group"
  [ ("genTypedExpr generates well-typed terms", prop_genTypedExpr_typeof)
  , ("one preserves types across iterations", prop_norm_preserve)
  , ("traced terms have TRACE type after some normalization", prop_trace_type)
  , ("norm . value . trace is in oneNF", prop_norm_onenf)
  , ("LINEAGE . TRACE = LINEAGE", prop_lineagetf_tracetf)
  , ("TRACE idempotent", prop_tracetf_idempotent)
  -- , ("`value` of traced terms has same type", prop_trace_value_type)
  ]

comment :: String -> IO ()
comment s = do
  _ <- replicateM 5 (putStrLn "")
  putStrLn s
  putStrLn (take (length s) (repeat '-'))

printNWL q qt normsteps unrollsteps = do
  -- let tq = (!! 400) . iterate one $ unroll 5 $ trace q
  let tq = trace (annVars q)

  comment "the query (normalized)"
  putE q

  comment "value of the query (normalized)"
  let vtq = (!! normsteps) . iterate one $ unroll unrollsteps $ value :§ T.App T.tracetf (T.List qt) :$ tq
  putE vtq

  comment "wherep of the query (normalized)"
  let wtq = (!! normsteps) . iterate one $ unroll unrollsteps $ wherep :§ T.App T.tracetf (T.List qt) :$ tq
  putE wtq

  comment "lineage of the query (normalized)"
  let ltq = (!! normsteps) . iterate one $ unroll unrollsteps $ lineage :§ T.App T.tracetf (T.List qt) :$ tq
  putE ltq


someFunc :: IO ()
someFunc = do
  {-
  showTraced $ Empty T.Bool
  showTraced $ Singleton true
  showTraced $ Singleton (Singleton true)
  showTraced $ Concat [Empty T.Bool, Singleton true]
  showTraced $ If true false true
  showTraced $ If true (If false (string "then then") (string "then else"))
                       (If true (string "else then") (string "else else"))
  showTraced $ Concat [If true (Singleton true) (Empty T.Bool), Singleton false]
  showTraced $ If true (Concat [Singleton true, Singleton false]) (Empty T.Bool)

  showTraced $ for "x" T.Bool (Singleton true) (Singleton true)
  showTraced $ for "x" (T.List T.Bool) (Singleton (Singleton true)) (If true ((Var "x") ::: (T.List T.Bool)) (Singleton false))

  putE $ annVars $ for "x" (T.List T.Bool) (Singleton (Singleton true)) (If true (Var "x") (Singleton false))

  let crab = T.Record (T.RowCons "a" T.String (T.RowCons "b" T.Bool T.RowNil))
  let tableABs = Table "abs" crab
  showTraced $ tableABs

  let xFromTable = for "x" crab tableABs (Singleton (Var "x" ::: crab))
  showTraced $ xFromTable
  let asFromTable = for "x" crab tableABs (Singleton (Proj "a" (Var "x" ::: crab)))
  showTraced $ asFromTable

  let bsFromTable = for "x" crab tableABs (Singleton (Proj "b" (Var "x" ::: crab)))
  showTraced $ for "y" T.Bool bsFromTable $ If (Var "y" ::: T.Bool) (Singleton (int 1)) (Empty T.Int)
  -}

  -- let fl = Eq T.Bool true true
  -- putE fl
  -- putE (trace fl)
  -- let vfl = value :§ T.Trace T.Bool :$ trace fl
  -- putE $ (!! 10) . iterate one $ unroll 2 $ vfl
  
  -- putStrLn "------ random term -------"
  -- ty <- Gen.sample T.genType
  -- putC ty
  -- ex <- Gen.sample (genTypedExpr [] (T.List ty))
  -- putE ex
  -- n <- Gen.sample (Gen.small (Gen.int (Range.exponential 2 1000)))
  -- putStrLn (show n)

  -- putE (Concat (map (Singleton . int) [1 .. 5]))
  -- let n = (!! 100) . iterate one $ ex
  -- putE $ n
  -- putC (typeof ex)
  -- putC (typeof n)

  -- let resultType = T.List (T.record [("department", T.String)
                                    -- ,("people", T.List (T.record [("name", T.String)
                                                                 -- ,("tasks", T.List T.String)]))])
  -- putStrLn (show (S.paths resultType))
  -- forM_ (S.paths resultType) (\p -> putC (S.outerShredding p resultType))

  let departmentsRT = T.record [("name", T.String)]
  let departments = Table "departments" departmentsRT
  let employeesRT = T.record [("dept", T.String)
                             ,("name", T.String)
                             ,("salary", T.Int)]
  let employees = Table "employees" employeesRT
  let contactsRT = T.record [("dept", T.String)
                            ,("name", T.String)
                            ,("client", T.Bool)]
  let contacts = Table "contacts" contactsRT
  let tasksRT = T.record [("employee", T.String)
                         ,("task", T.String)]
  let tasks = Table "tasks" tasksRT

  let contactsOfDept = lam "d" departmentsRT $
                         for "c" contacts $
                           If (Eq T.String (Proj "name" (Var "d")) (Proj "dept" (Var "c")))
                              (Singleton (Record [("client", Proj "client" (Var "c"))
                                                 ,("name", Proj "name" (Var "c"))]))
                              (Empty (T.record [("client", T.Bool), ("name", T.String)]))

  let tasksOfEmp = lam "e" employeesRT $
                     for "t" tasks $
                       If (Eq T.String (Proj "employee" (Var "t")) (Proj "name" (Var "e")))
                          (Singleton (Proj "task" (Var "t")))
                          (Empty T.String)
  
  let employeesOfDept = lam "d" departmentsRT $
                          for "e" employees $
                            If (Eq T.String (Proj "name" (Var "d")) (Proj "dept" (Var "e")))
                               (Singleton (Record [("name", Proj "name" (Var "e"))
                                                  ,("salary", Proj "salary" (Var "e"))
                                                  ,("tasks", tasksOfEmp :$ Var "e")]))
                               (Empty (T.record [("name", T.String)
                                                ,("salary", T.Int)
                                                ,("tasks", T.List T.String)]))
  
  let benchQ1 = for "d" departments $
                  Singleton $ Record $ [("contacts", contactsOfDept :$ Var "d")
                                       ,("employees", employeesOfDept :$ Var "d")
                                       ,("name", Proj "name" (Var "d"))]
  putE benchQ1
  let tBenchQ1 = trace ((!! 145) . iterate one $ annVars benchQ1)
  -- putE $ (!! 145) . iterate one $ unroll 3 $ tBenchQ1
  let vBenchQ1 = (!! 1450) . iterate one $ unroll 12 $ (value :§ (T.App T.tracetf (T.List (T.record [("contacts", T.List (T.record [("client", T.Bool), ("name", T.String)]))
                                                                                                  ,("employees", T.List (T.record [("name", T.String)
                                                                                                                                  ,("salary", T.Int)
                                                                                                                                  ,("tasks", T.List T.String)]))
                                                                                                  ,("name", T.String)]))) :$ tBenchQ1)
  putE vBenchQ1

  let wBenchQ1 = (!! 1450) . iterate one $ unroll 12 $ wherep :§ (T.App T.tracetf (T.List (T.record [("contacts", T.List (T.record [("client", T.Bool), ("name", T.String)]))
                                                                                                  ,("employees", T.List (T.record [("name", T.String)
                                                                                                                                  ,("salary", T.Int)
                                                                                                                                  ,("tasks", T.List T.String)]))
                                                                                                  ,("name", T.String)]))) :$ tBenchQ1
  putE wBenchQ1


  -- putE $ wherep
  let agenciesRecordType = (T.record [("based_in", T.String)
                                     ,("name", T.String)
                                     ,("phone", T.String)])
  let agencies = Table "agencies" agenciesRecordType

  let externalToursRecordType = (T.record [("destination", T.String)
                                          ,("name", T.String)
                                          ,("price", T.Int)
                                          ,("type", T.String)])
  let externalTours = Table "externalTours" externalToursRecordType
  let boatToursrt = T.record [("name", T.String)
                      ,("phone", T.String)]
  let boatTours = for "a" agencies $
           for "e" externalTours $
           If (And
              -- a.name == e.name
               (Eq T.String (Proj "name" (Var "a" ::: agenciesRecordType)) (Proj "name" (Var "e" ::: externalToursRecordType)))
               -- e.type == "boat"
               (Eq T.String (Proj "type" (Var "e" ::: externalToursRecordType)) (Const (String "boat"))))
             (Singleton (Record [("name", Proj "name" (Var "e" ::: externalToursRecordType))
                                ,("phone", Proj "phone" (Var "a" ::: agenciesRecordType))]))
             (Empty boatToursrt)
  comment "Boat tours"
  putE $ boatTours
  comment "Self-tracing boat tours (⊥ is `value`)"
  putE (unroll 0 $ trace boatTours)
  comment "Normalized self-tracing boat tours"
  let tboatTours = (!! 145) . iterate one $ unroll 3 $ trace boatTours
  putE tboatTours

  comment "value"
  putE value

  comment "1. boat tours; 2. normalized value of trace of boat tours"
  let vtboatTours = (!! 145) . iterate one $ unroll 6 $ (value :§ (T.App T.tracetf (T.List boatToursrt)) :$ tboatTours)
  putE boatTours
  putStrLn "--------------"
  putE vtboatTours

  comment "where-prov of trace of boat tours (normalized)"
  let wtboatTours = (!! 145) . iterate one $ unroll 6 $ (wherep :§ (T.App T.tracetf (T.List boatToursrt)) :$ tboatTours)
  putE wtboatTours

  comment "lineage of trace of boat tours (normalized)"
  let ltboatTours = (!! 145) . iterate one $ unroll 7 $ (lineage :§ (T.App T.tracetf (T.List boatToursrt)) :$ tboatTours)
  putE ltboatTours

  comment "example of duplication"
  let et = T.record [("a", T.Int), ("b", T.Bool), ("c", T.String)]
  let eq = for "x" (Table "xs" et) $ Singleton (Proj "a" (Var "x"))
  putE eq
  -- let teq = trace (annVars eq)
  let steq = (!! 7) . iterate one $ trace (annVars eq)
  -- putE teq
  putE steq
  let lteq = (!! 145) . iterate one $ unroll 7 $ lineage :§ (T.App T.tracetf (T.List T.Int)) :$ steq
  putE lteq

  let presidentsT = T.record [("nth", T.Int), ("name", T.String)]
  let inaugurationsT = T.record [("nth", T.Int), ("term", T.Int), ("date", T.String)]
  let metroT = T.record [("date", T.String), ("time", T.Int), ("trips", T.Int)]
  
  -- for (p <-- presidents)
    -- [(name = p.name,
      -- dates = for (i <-- inaugurations) where (i.nth == p.nth)
              -- for (m <-- metro) where (m.date == i.date &&
                     -- m.time == 11 && m.trips >= 193000)
                -- [i.date])]
  let q = annVars $ for "p" (Table "presidents" presidentsT) (Singleton (Record [("name", Proj "name" (Var "p")), ("dates", for "i" (Table "inaugurations" inaugurationsT) $
               for "m" (Table "metro" metroT) $
               If (And (Eq T.Int (Proj "nth" (Var "i")) (Proj "nth" (Var "p"))) (And (Eq T.String (Proj "date" (Var "m")) (Proj "date" (Var "i"))) (And (Eq T.Int (Proj "time" (Var "m")) (Const (Int 11))) (GEq (Proj "trips" (Var "m")) (Const (Int 193000))))))
                  (Singleton (Proj "date" (Var "i")))
                  (Empty T.String))]))

  let tq = (!! 400) . iterate one $ unroll 5 $ trace q
  -- putE q
  let qrt = T.record [("name", T.String), ("dates", T.List T.String)]

  comment "1. query from llinks chapter; 2. normalized value of that query"
  let vtq = (!! 400) . iterate one $ unroll 10 $ (value :§ (T.App T.tracetf (T.List qrt)) :$ tq)
  putE q
  putStrLn "--------------"
  putE vtq

  comment "where-prov of trace of llinks query (normalized)"
  let wtq = (!! 300) . iterate one $ unroll 10 $ (wherep :§ (T.App T.tracetf (T.List qrt)) :$ tq)
  putE wtq

  comment "lineage of trace of llinks query (normalized)"
  let ltq = (!! 600) . iterate one $ unroll 20 $ (lineage :§ (T.App T.tracetf (T.List qrt)) :$ tq)
  putE ltq

  -- var QC4 = for (x <-- employees) for (y <-- employees)
          -- where (x.dept == y.dept && x.name <> y.name)
  -- [(a=x.name, b=y.name,
    -- c=(for (t <-- tasks) where (x.name == t.employee) 
         -- [(doer="a", task=t.task)]) 
       -- ++ (for (t <-- tasks) where (y.name == t.employee)
            -- [(doer="b", task=t.task)]))];

  -- let qc4 = for "x" (Table "employees" employeesT) (for "y" (Table "employees" employeesT) (If (And (Eq T.String (Proj "dept" (Var "x")) (Proj "dept" (Var "y"))) (Eq _) (Singleton (Record [("a", Proj "name" (Var "x")), ("b", Proj "name" (Var "y")), ("c", Concat (for "t" (Table "tasks" tasksT) (If (Eq T.String (Proj "name" (Var "x")) (Proj "employee" (Var "t"))) (Singleton (Record [("doer", Const (String "a")), ("task", Proj "task" (Var "t"))])))) (for "t" (Table "tasks" tasksT) (If (Eq T.String (Proj "name" (Var "y")) (Proj "employee" (Var "t"))) (Singleton (Record [("doer", Const (String "b")), ("task", Proj "task" (Var "t"))])))))])) (Empty _))

  -- var QF4 =
  -- (for (t <-- tasks) where (t.task == "abstract") [t.employee]) ++
  -- (for (e <-- employees) where (e.salary > 50000) [e.name]);
  let tasksT = T.record [("employee", T.String), ("task", T.String)]
  let employeesT = T.record [("dept", T.String), ("name", T.String), ("salary", T.Int)]
  
  let qf4 = Concat [for "e" (Table "employees" employeesT) (If (GEq (Const (Int 50000)) (Proj "salary" (Var "e"))) (Singleton (Proj "name" (Var "e"))) (Empty T.String))
                   ,for "t" (Table "tasks" tasksT) (If (Eq T.String (Proj "task" (Var "t")) (Const (String "abstract"))) (Singleton (Proj "employee" (Var "t"))) (Empty T.String))]
  let qf4t = T.String

  printNWL qf4 qf4t 100 10

  -- recheck (Size 6) (Seed 4698711793314857007 (-2004285861016953403)) prop_norm_onenf
  -- recheck (Size 8) (Seed 2462093613668237218 (-6374363080471542215)) prop_norm_onenf
  -- recheck (Size 25) (Seed 6220584399433914846 (-6790911531265473973)) prop_norm_onenf
  -- recheck (Size 57) (Seed 3580701760170488301 (-3044242196768731585)) prop_norm_onenf

  -- pure ()
  void tests
