{-# LANGUAGE TupleSections #-}
module Lib where

import Control.Monad.State.Strict

type Variable = Int 

data Ty
  = Basic String
  | StringT
  | Arrow Ty Ty
  | RecordT [(String, Ty)]
  | VariantT [(String, Ty)]
  | UnknownT
  deriving (Show)

data Tm
  = Var Variable
  | Lam Variable Tm
  | Str String
  | App Tm Tm
  | Record [(String, Tm)] -- do I want a special label type instead? more implementation effort, but it might be clearer what's going on..
  | DynProj Tm Tm
  deriving (Eq, Show)

data Sem
  = LAM (Sem -> State Int Sem)
  | RECORD [(String, Sem)]
  | STRING String
  | SYN Tm

freshVariable :: State Int Int
freshVariable = state (\s -> (s, s+1))


reflect :: Ty -> Tm -> State Int Sem
reflect (Arrow a b) t =
  return $ LAM (\s -> do
                   s' <- reify a s
                   reflect b (App t s'))
reflect (RecordT flds) t = do
  flds <- traverse (\(l, x) -> (l,) <$> reflect x (DynProj (Str l) t)) flds
  return (RECORD flds)
-- reflect StringT (Str t) = return (STRING t)
reflect StringT (DynProj l t) = do
  -- Ugh. I guess I can see whether I succeeded in evaluating things away? Is that needed? I'm confused.
  -- l <- reflect StringT l
  -- case l of
    -- STRING l -> 
  -- t <- reflect (RecordT [ 
  return (SYN (DynProj l t))
reflect (Basic _) t = return (SYN t)
-- reflect ty tm = error $ show ty

reify :: Ty -> Sem -> State Int Tm
reify (Arrow a b) (LAM s) = do
  x <- freshVariable
  ra <- reflect a (Var x)
  sra <- s ra
  rb <- reify b sra
  return (Lam x rb)
reify (RecordT fieldTypes) (RECORD fieldSemantics) = do
  fields <- traverse (\((l, fieldType), (l', fieldSemantics)) ->
                        (l,) <$> reify fieldType fieldSemantics)
              (zip fieldTypes fieldSemantics)
  return (Record fields)
reify StringT (STRING s) = return (Str s)
reify StringT (SYN t) = return t -- huh should should this be the case?: reify _ (SYN t) = t
reify (Basic _) (SYN t) = return t
reify t s = error (show t)


eval :: [(Variable, Sem)] -> Tm -> State Int Sem
eval env (Var x) = case lookup x env of
                     Just v -> return v
eval env (Lam x b) =
  return (LAM (\s -> eval ((x, s):env) b))
eval env (App s t) = do
  LAM s <- eval env s
  t <- eval env t
  s t
eval env (Record fields) = do
  fields <- traverse (\(l, x) -> (l,) <$> eval env x) fields
  return (RECORD fields)
eval env (DynProj l r) = do
  STRING l <- eval env l
  RECORD r <- eval env r
  case lookup l r of
    Just v -> return v
    Nothing -> error "not a label in record"
eval env (Str s) = return (STRING s)
  

nbe :: Ty -> Tm -> Tm
nbe a t = flip evalState 0 $ do
  e <- eval [] t
  reify a e

fst3 (x, _, _) = x

lookupBy f x [] = Nothing
lookupBy f x (y:ys) | f y == x = Just y
lookupBy f x (_:ys) = lookupBy f x ys
