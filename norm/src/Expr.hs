{-# OPTIONS_GHC -fwarn-incomplete-patterns 
#-}
--  -Werror=incomplete-patterns
module Expr where

import Type (Type)
import qualified Type as T
import Control.Exception (assert)
import Data.Maybe (fromJust)

mapSnd :: (b -> c) -> [(a, b)] -> [(a, c)]
mapSnd f = map (\(l, x) -> (l, f x))

mapThd :: (c -> d) -> [(a, b, c)] -> [(a, b, d)]
mapThd f = map (\(l, y, x) -> (l, y, f x))

lookup3 :: Eq t => t -> [(t, b, c)] -> Maybe (t, b, c)
lookup3 _ [] = Nothing
lookup3 l (t@(l', _, _):xs) = if l == l' then Just t else lookup3 l xs

type Var = Integer
type Label = String

data Const
  = Bool Bool
  | String String
  | Eq
  | And
  deriving (Show)

data Expr
  = Var Var Type
  | Const Const
  | Lam Var Expr
  | Expr :$ Expr
  | Rec [(Label, Expr)]
  | Expr :. Label
  | If Expr Expr Expr
  | Singleton Expr | Concat [Expr]
  | For Var Expr Expr
  | Table String Type
  | Label :| Expr
  | Case Expr [(Label, Var, Expr)]
  deriving (Show)

-- M[x := N]
--       M       x      N
subst :: Expr -> Var -> Expr -> Expr
subst expression var substitution = go expression
  where go (Var v _) | v == var = substitution
        go v@Var{} = v
        go c@Const{} = c
        go (Lam v e) = assert (v /= var) (Lam v (go e))
        go (a :$ b) = go a :$ go b
        go (Rec es) = Rec (mapSnd go es)
        go (e :. l) = go e :. l
        go (If a b c) = If (go a) (go b) (go c)
        go (Singleton e) = Singleton (go e)
        go (Concat as) = Concat (map go as)
        go (For v i o) = assert (v /= var) (For v (go i) (go o))
        go t@Table{} = t
        go (l :| e) = l :| go e
        go (Case v cs) = Case (go v) (mapThd go cs)

symev :: [(Var, Expr)] -> Expr -> Expr
symev env (Var x t) = case lookup x env of
  Nothing -> error $ "unbound variable " ++ show x
  Just v -> v
symev env (Const c) = Const c
symev env ((Const And :$ a) :$ b) = reduceAnd (symev env a) (symev env b)
symev env ((Const Eq :$ a) :$ b) = reduceEq (symev env a) (symev env b)
symev env (f :$ p) = app (symev env f) (symev env p)
  where
    app (Lam x n) m = subst n x m
    app (If c t e) args =
      reduceIfCond c (app t args) (app e args)
    app e a = error $ "app: " ++ show e ++ " :$ " ++ show a
symev env (For x (Singleton m) n) = subst n x m
symev env (For x m n) = For x (symev env m)
  (symev ((x, Var x T.String):env) n) -- TODO fix type
symev env (Table n t) = Table n t
symev env (r :. l) =
  proj r
  where
    proj (Rec fields) = fromJust (lookup l fields)
    proj (If c t e) = If c (proj t) (proj e)
    proj (Var x (T.Rec row)) = Var x (T.Rec row) :. l
    proj _ = error "error projecting from record"
symev env (If c t e) =
  reduceIfCond (symev env c) (symev env t) (symev env e)
symev env (Lam x b) = Lam x (symev env b)
symev env (Singleton e) = Singleton (symev env e)
symev env (Concat l) = Concat (map (symev env) l)
symev env (Rec fields) = Rec (mapSnd (symev env) fields)
symev env (l :| e) = l :| symev env e
symev env (Case v cs) = reduceCase (symev env v) cs
  where reduceCase (l :| e) cases = case lookup3 l cases of
          Nothing -> error $ "unmatched case " ++ l
          Just (_, var, body) -> symev ((var,e):env) body
        reduceCase (If c t e) cases = If c (reduceCase t cases) (reduceCase e cases)
        reduceCase wtf _ = error $ "missing comm conv or bug? " ++ show wtf

reduceIfCond :: Expr -> Expr -> Expr -> Expr
reduceIfCond (Const (Bool True)) t _ = t
reduceIfCond (Const (Bool False)) _ e = e
reduceIfCond c t e = reduceIfBody c t e

reduceIfBody :: Expr -> Expr -> Expr -> Expr
reduceIfBody c (Rec ifFields) (Rec thenFields) = assert (map fst ifFields == map fst thenFields)
  error "todo"
reduceIfBody c t e = If c t e

reduceAnd :: Expr -> Expr -> Expr
reduceAnd a b = Const And :$ a :$ b

reduceEq :: Expr -> Expr -> Expr
reduceEq a b = Const Eq :$ a :$ b

tourType :: Type
tourType = T.closedRec
  [("name", T.String), ("dest", T.String), ("type", T.String)]

agencyType :: Type
agencyType = T.closedRec
  [("name", T.String), ("destination", T.String), ("phone", T.String)]

-- fun (tour) { tour.type == "boat" }
isBoatTour :: Expr
isBoatTour =
  Lam 0 (Const Eq
          :$ (Var 0 tourType :. "type")
          :$ Const (String "boat"))

-- for (a <- agencies) for (t <- tours) where (a.name == t.name && isBoatTour t) [(name = t.name, phone = a.phone)]
boatTours :: Expr
boatTours =
  For 1 (Table "agencies" agencyType)
  (For 2 (Table "tours" tourType)
    (If ((Const And
          :$ (Const Eq
               :$ (Var 1 agencyType :. "name")
               :$ (Var 2 tourType :. "name")))
          :$ (isBoatTour :$ Var 2 tourType))
     (Singleton (Rec [ ("name", Var 2 tourType :. "name")
                     , ("phone", Var 1 agencyType :. "phone") ]))
     (Concat [])))

tAgencies = For 3 (Table "agencies" agencyType)
  (Singleton (Rec [("name", "Row" :| Rec [("table", Const (String "agencies"))
                                         ,("data", Var 3 agencyType :. "name")])]))

untracedAgencies = For 4 (tAgencies)
  (Singleton (Rec [("name", Case (Var 4 T.String) [("Row", 5, Var 5 T.String :. "name" :. "data")])]))
