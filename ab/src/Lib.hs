{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, GADTs, KindSignatures, MultiParamTypeClasses, RankNTypes, StandaloneDeriving, TypeSynonymInstances #-}

module Lib where

import Control.Monad.Trans.State.Strict
import Data.Maybe (fromJust)

type Var = String

data Ty
  = A
  | B
  | C
  | ArrT Ty Ty
  | SumT Ty Ty

data Exp
  = Var Var
  | Lam Var Exp
  | App Exp Exp
  | Inl Exp
  | Inr Exp
  | Case Exp Var Exp Var Exp
  | Let Var Exp Exp
  deriving (Show)

class CompLam exp where
  lam :: (exp -> exp) -> exp
  app :: exp -> exp -> exp
  inl :: exp -> exp
  inr :: exp -> exp
  case_ :: exp -> (exp -> exp) -> (exp -> exp) -> exp
  let_ :: exp -> (exp -> exp) -> exp

type Hoas = forall exp. CompLam exp => exp

hoasToExp :: Hoas -> Exp
hoasToExp v = evalGen v 0

instance CompLam (Gen Exp) where
  lam f = do
    x <- nextName
    e <- f (return (Var x))
    return $ Lam x e
  app v1 v2 = do
    e1 <- v1
    e2 <- v2
    return $ App e1 e2
  inl v = do e <- v; return $ Inl e
  inr v = do e <- v; return $ Inr e
  case_ v l r = do
    e <- v
    x1 <- nextName
    x2 <- nextName
    e1 <- l (return (Var x1))
    e2 <- r (return (Var x2))
    return $ Case e x1 e1 x2 e2
  let_ v f = do
    e <- v
    x <- nextName
    e' <- f (return (Var x))
    return $ Let x e e'

type Gen = State Int

nextName :: Gen Var
nextName = do
  i <- get
  put (i+1)
  return ("x" ++ show i)

evalGen :: Gen a -> Int -> a
evalGen = evalState

type Env a = [(Var, a)]

empty :: Env a
empty = []

extend :: Env a -> Var -> a -> Env a
extend env x v = (x, v) : env

data SemV = Neutral Exp
          | Fun (SemV -> SemC)
          | Sum (Either SemV SemV)

type SemC = GenAcc SemV

eval :: Env SemV -> Exp -> GenAcc SemV
eval env (Var x) = return (fromJust (lookup x env))
eval env (Lam x e) = return (Fun (\v -> eval (extend env x v) e))
eval env (App e1 e2) = do
  Fun v1 <- eval env e1
  v2 <- eval env e2
  v1 v2
eval env (Let x e1 e2) = do
  v <- eval env e1
  eval (extend env x v) e2
eval env (Inl e) = do
  v <- eval env e
  return (Sum (Left v))
eval env (Inr e) = do
  v <- eval env e
  return (Sum (Right v))
eval env (Case e x1 e1 x2 e2) = do
  Sum v <- eval env e
  case v of
    Left v -> eval (extend env x1 v) e1
    Right v -> eval (extend env x2 v) e2


data Acc a = Val a
           | LetB Var Exp (Acc a)
           | CaseB Exp Var (Acc a) Var (Acc a)
  deriving (Functor)

instance Applicative Acc where
  pure = Val
  -- (<*>) = _

instance Monad Acc where
  return = Val
  Val v >>= f = f v
  LetB x e m >>= f = LetB x e (m >>= f)
  CaseB e x1 m1 x2 m2 >>= f = CaseB e x1 (m1 >>= f) x2 (m2 >>= f)

flatten :: Acc Exp -> Exp
flatten (Val e) = e
flatten (LetB x e t) = Let x e (flatten t)
flatten (CaseB v x1 t1 x2 t2) =
  Case v x1 (flatten t1) x2 (flatten t2)

newtype GenAcc a = GA {unGA :: Gen (Acc a)}

deriving instance Functor GenAcc

instance Applicative GenAcc where
  pure = GA . pure . pure

instance Monad GenAcc where
  return = GA . return . return
  m >>= k =
    GA (do c <- unGA m
           case c of
             Val v -> unGA (k v)
             LetB x e m -> do
               t <- unGA (GA (return m) >>= k)
               return (LetB x e t)
             CaseB e x1 m1 x2 m2 -> do
               t1 <- unGA (GA (return m1) >>= k)
               t2 <- unGA (GA (return m2) >>= k)
               return (CaseB e x1 t1 x2 t2))

gamma :: Gen a -> GenAcc a
gamma f = GA (do v <- f; return (return v))

collect :: GenAcc Exp -> Gen Exp
collect (GA f) = do t <- f; return (flatten t)

bind :: Exp -> GenAcc Var
bind e = GA (do x <- nextName; return $ LetB x e (Val x))

binds :: Exp -> GenAcc (Either Var Var)
binds e = GA $ do
  x1 <- nextName
  x2 <- nextName
  return $ CaseB e x1 (Val (Left x1)) x2 (Val (Left x2))


reifyC :: Ty -> SemC -> Gen Exp
reifyC a c = collect (do v <- c; gamma (reifyV a v))

reifyV :: Ty -> SemV -> Gen Exp
reifyV A (Neutral e) = return e
reifyV B (Neutral e) = return e
reifyV C (Neutral e) = return e
reifyV (ArrT a b) (Fun f) = do
  x <- nextName
  e <- reifyC b (do v <- reflectV a x; f v)
  return $ Lam x e
reifyV (SumT a b) (Sum (Left v)) = do
  e <- reifyV a v
  return $ Inl e
reifyV (SumT a b) (Sum (Right v)) = do
  e <- reifyV a v
  return $ Inr e

reflectV :: Ty -> Var -> SemC
reflectV A x = return (Neutral (Var x))
reflectV B x = return (Neutral (Var x))
reflectV C x = return (Neutral (Var x))
reflectV (ArrT a b) x =
  return (Fun (\v -> do e <- gamma (reifyV a v); reflectC b x e))
reflectV (SumT a b) x = do
  v <- binds (Var x)
  case v of
    Left x1 -> do v1 <- reflectV a x1
                  return (Sum (Left v1))
    Right x2 -> do v2 <- reflectV b x2
                   return (Sum (Right v2))

reflectC :: Ty -> Var -> Exp -> SemC
reflectC a x e = do
  x <- bind (App (Var x) e)
  reflectV a x

norm :: Ty -> Hoas -> Exp
norm a e = evalGen (reifyC a (eval empty (hoasToExp e))) 0


ex1 = norm (ArrT A A) (lam (\x -> x))
ex2 = norm (ArrT (ArrT A A) (ArrT A A)) (lam (\x -> x))
ex3 = norm (ArrT (SumT A B) (SumT A B)) (lam (\x -> x))
