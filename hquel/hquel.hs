{-# LANGUAGE NoMonomorphismRestriction, InstanceSigs #-}

data Product = Product Int String Int
  deriving Show

data Order = Order Int Int Int
  deriving Show

-- class SCHEMA repr where
--   product :: repr Int -> repr String -> repr Int -> Product
--   pid :: repr Product -> repr Int
--   name :: repr Product -> repr String
--   price :: repr Product -> repr Int
--   products :: () -> [Product]

-- orders :: () -> [Order]
-- products :: () -> [Product]
-- orders = undefined
-- products = undefined

-- Questions:
--  - OCaml version uses () -> a for delaying evaluation.
--    Haskell is lazy. Do we still need this?
--    Apparently not.. as in, I removed it, it still seems to work.
class Symantics repr where
  -- product :: repr Int -> repr String -> repr Int -> Product
  -- p_pid :: repr Product -> repr Int
  -- name :: repr Product -> repr String
  -- price :: repr Product -> repr Int
  -- products :: repr [Product]
  -- -- repr is missing in Figure 7. Should it be there?
  -- -- their code does not have it either, so probably not...
  -- -- might be repr (() -> [Product])
  -- -- see what makes sense later..

  -- order :: repr Int -> repr Int -> repr Int -> Order
  oid :: repr Order -> repr Int 
  -- o_pid :: repr Order -> repr Int 
  -- qty :: repr Order -> repr Int
  orders :: repr [Order]

  int :: Int -> repr Int
  -- bool :: Bool -> repr Bool
  -- string :: String -> repr String
  -- lam :: (repr a -> repr b) -> repr (a -> b)
  -- app :: repr (a -> b) -> repr a -> repr b
  for :: repr [a] -> (repr a -> repr [b]) -> repr [b]
  where' :: repr Bool -> repr [a] -> repr [a]
  yield :: repr a -> repr [a]
  nil :: repr [a]
  -- union :: repr [a] -> repr [a] -> repr [a]
  equals :: Eq a => repr a -> repr a -> repr Bool

fortytwo = int 42

q1 :: Symantics repr => repr Int -> repr [Order]
q1 xoid = for orders $ (\o -> where' (equals (oid o) xoid) $ yield o)

data R a = R{eval:: a}

append :: [a] -> [a] -> [a]
append = mappend

instance Symantics R where
  int = R
  for :: R [a] -> (R a -> R [b]) -> R [b]
  for tbl f = case tbl of
                R []     -> R []
                R (x:xs) -> R (eval (f (R x)) `append` (eval (for (R xs) f)))
  where' (R p) e = if p then e else R []
  oid (R (Order oid _ _)) = R oid
  yield (R x) = R [x]
  nil = R []
  orders = R [Order 1 1 5, Order 1 2 5, Order 1 4 2, Order 2 5 10, Order 2 6 20, Order 3 2 50]
  equals (R a) (R b) = R (a == b)

res_q1_2 = eval (q1 (int 2))
