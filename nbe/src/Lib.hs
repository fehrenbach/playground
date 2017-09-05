module Lib where

someFunc :: IO ()
someFunc = putStrLn "someFunc"

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
  = LAM (Sem -> Sem)
  | PAIR (Sem, Sem)
  | SYN Tm

type State = Int

reflect :: Ty -> Tm -> Sem
reflect (Arrow a b) t =
  LAM (\s -> reflect b (App t (reify a s)))
reflect (Prod a b) t =
  PAIR (reflect a (Fst t), reflect b (Snd t))
reflect (Basic _) t = SYN t

reify :: Ty -> Sem -> Tm
reify (Arrow a b) (LAM s) =
  let x = _
  in Lam x (reify b (s (reflect a (Var x))))
reify (Prod a b) (PAIR (s, t)) =
  Pair (reify a s) (reify b t)
reify (Basic _) (SYN t) = t

eval :: [(Variable, Sem)] -> Tm -> Sem
eval env (Var x) = case lookup x env of
                     Just v -> v
eval env (Lam x b) = LAM (\s -> eval ((x, s):env) b)
eval env (App s t) = case eval env s of
                       LAM s -> s (eval env t)
eval env (Pair s t) = PAIR (eval env s, eval env t)
eval env (Fst p) = case eval env p of
                     PAIR (s, t) -> s
eval env (Snd p) = case eval env p of
                     PAIR (s, t) -> t

nbe :: Ty -> Tm -> Tm
nbe a t = reify a (eval [] t)

k = Lam 0 (Lam 1 (Var 0))
s = Lam 0 (Lam 1 (Lam 2 (App (App (Var 0) (Var 2)) (App (Var 1) (Var 2)))))
skk = App (App s k) k

idt = Arrow (Basic "a") (Basic "a")
idt' = Arrow (Arrow (Basic "a") (Basic "b")) (Arrow (Basic "a") (Basic "b"))
