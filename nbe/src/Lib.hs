module Lib where

import Control.Monad.State.Strict

type Variable = Int 

data Ty
  = Basic String
  | Arrow Ty Ty
  | Prod Ty Ty

data Tm
  = Var Variable
  | Lam Variable Tm
  | App Tm Tm
  | Pair Tm Tm
  | Fst Tm
  | Snd Tm
  deriving (Show)

data Sem
  = LAM (Sem -> State Int Sem)
  | PAIR (Sem, Sem)
  | SYN Tm

freshVariable :: State Int Int
freshVariable = state (\s -> (s, s+1))

reflect :: Ty -> Tm -> State Int Sem
reflect (Arrow a b) t =
  return $ LAM (\s -> do
                   s' <- reify a s
                   reflect b (App t s'))
reflect (Prod a b) t = do
  a <- reflect a (Fst t)
  b <- reflect b (Snd t)
  return (PAIR (a, b))
reflect (Basic _) t = return (SYN t)

reify :: Ty -> Sem -> State Int Tm
reify (Arrow a b) (LAM s) = do
  x <- freshVariable
  ra <- reflect a (Var x)
  sra <- s ra
  rb <- reify b sra
  return (Lam x rb)
reify (Prod a b) (PAIR (s, t)) = do
  a <- reify a s
  b <- reify b t
  return (Pair a b)
reify (Basic _) (SYN t) = return t

eval :: [(Variable, Sem)] -> Tm -> State Int Sem
eval env (Var x) = case lookup x env of
                     Just v -> return v
eval env (Lam x b) =
  return (LAM (\s -> eval ((x, s):env) b))
eval env (App s t) = do
  LAM s <- eval env s
  t <- eval env t
  s t
eval env (Pair s t) = do
  s <- eval env s
  t <- eval env t
  return (PAIR (s, t))
eval env (Fst p) = do
  PAIR (s, t) <- eval env p
  return s
eval env (Snd p) = do
  PAIR (s, t) <- eval env p
  return t

nbe :: Ty -> Tm -> Tm
nbe a t = flip evalState 100 $ do
  e <- eval [] t
  reify a e

k = Lam 0 (Lam 1 (Var 0))
s = Lam 0 (Lam 1 (Lam 2 (App (App (Var 0) (Var 2)) (App (Var 1) (Var 2)))))
skk = App (App s k) k

idt = Arrow (Basic "a") (Basic "a")
idt' = Arrow (Arrow (Basic "a") (Basic "b")) (Arrow (Basic "a") (Basic "b"))
