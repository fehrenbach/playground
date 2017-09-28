{-# LANGUAGE DeriveFunctor, FlexibleInstances, GADTs, KindSignatures, MultiParamTypeClasses, RankNTypes, StandaloneDeriving, TypeSynonymInstances #-}

module Lib where

import Control.Monad.Trans.State.Strict
import Data.Maybe (fromJust)

type Var = String

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

data A
data B
data C

data Rep :: * -> * where
  A :: Rep A
  B :: Rep B
  C :: Rep C
  ArrT :: Rep a -> Rep b -> Rep (a -> b)
  SumT :: Rep a -> Rep b -> Rep (Either a b)

class Representable a where
  rep :: Rep a

instance Representable A where rep = A
instance Representable B where rep = B
instance Representable C where rep = C

instance (Representable a, Representable b) => Representable (a -> b) where
  rep = ArrT rep rep

instance (Representable a, Representable b) => Representable (Either a b) where
  rep = SumT rep rep

class Monad m => Residualising m where
  gamma :: Gen a -> m a
  collect :: m Exp -> Gen Exp
  bind :: Exp -> m Var
  binds :: Exp -> m (Either Var Var)

type Env a = [(Var, a)]

empty :: Env a
empty = []

extend :: Env a -> Var -> a -> Env a
extend env x v = (x, v) : env

class FunInt v m where
  injFun :: (v -> m v) -> m v
  projFun :: v -> (v -> m v)

class SumInt v where
  injSum :: Either v v -> v
  projSum :: v -> Either v v

eval :: (Monad m, FunInt a m, SumInt a) => Env a -> Exp -> m a
eval env (Var x) = return (fromJust (lookup x env))
eval env (Lam x e) = injFun (\v -> eval (extend env x v) e)
eval env (App e1 e2) = do
  v1 <- eval env e1
  v2 <- eval env e2
  projFun v1 v2
eval env (Let x e1 e2) = do
  v <- eval env e1
  eval (extend env x v) e2
eval env (Inl e) = do
  v <- eval env e
  return (injSum (Left v))
eval env (Inr e) = do
  v <- eval env e
  return (injSum (Right v))
eval env (Case e x1 e1 x2 e2) = do
  v <- eval env e
  case projSum v of
    Left v -> eval (extend env x1 v) e1
    Right v -> eval (extend env x2 v) e2

data SemV m = Neutral Exp
            | Fun (SemV m -> SemC m)
            | Sum (Either (SemV m) (SemV m))

type SemC m = m (SemV m)

instance Residualising m => FunInt (SemV m) m where
  injFun f = return (Fun f)
  projFun (Fun f) = f

instance Residualising m => SumInt (SemV m) where
  injSum = Sum
  projSum (Sum s) = s

type ResEval m = Env (SemV m) -> Exp -> SemC m

reifyC :: Residualising m => Rep a -> SemC m -> Gen Exp
reifyC a c = collect (do v <- c; gamma (reifyV a v))

reifyV :: Residualising m => Rep a -> SemV m -> Gen Exp
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

reflectV :: Residualising m => Rep a -> Var -> SemC m
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

reflectC :: Residualising m => Rep a -> Var -> Exp -> SemC m
reflectC a x e = do
  x <- bind (App (Var x) e)
  reflectV a x

normU :: Residualising m => ResEval m -> Rep a -> Hoas -> Exp
normU eval a e = evalGen (reifyC a (eval empty (hoasToExp e))) 0

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

instance Residualising GenAcc where
  gamma f = GA (do v <- f; return (return v))
  collect (GA f) = do t <- f; return (flatten t)
  bind e = GA (do x <- nextName; return $ LetB x e (Val x))
  binds e = GA $ do
    x1 <- nextName
    x2 <- nextName
    return $ CaseB e x1 (Val (Left x1)) x2 (Val (Left x2))

normAccU = normU (eval :: ResEval GenAcc)

ex1 = normAccU (rep :: Rep (A -> A)) (lam (\x -> x))
ex2 = normAccU (rep :: Rep ((A -> A) -> (A -> A))) (lam (\x -> x))
ex3 = normAccU (rep :: Rep (Either A B -> Either A B)) (lam (\x -> x))
