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
  p_pid :: repr Product -> repr Int
  name :: repr Product -> repr String
  price :: repr Product -> repr Int
  products :: repr [Product]
  -- -- repr is missing in Figure 7. Should it be there?
  -- -- their code does not have it either, so probably not...
  -- -- might be repr (() -> [Product])
  -- -- see what makes sense later..

  -- order :: repr Int -> repr Int -> repr Int -> Order
  oid :: repr Order -> repr Int 
  o_pid :: repr Order -> repr Int
  qty :: repr Order -> repr Int
  orders :: repr [Order]

  sale :: repr Int -> repr String -> repr Int -> repr Sale

  int :: Int -> repr Int
  -- bool :: Bool -> repr Bool
  -- string :: String -> repr String
  lam :: (repr a -> repr b) -> repr (a -> b)
  app :: repr (a -> b) -> repr a -> repr b
  for :: repr [a] -> (repr a -> repr [b]) -> repr [b]
  where' :: repr Bool -> repr [a] -> repr [a]
  yield :: repr a -> repr [a]
  nil :: repr [a]
  -- union :: repr [a] -> repr [a] -> repr [a]

  -- is this the way to do it?
  -- how to reuse the real names (*) and (==)?
  mult :: Num a => repr a -> repr a -> repr a
  equals :: Eq a => repr a -> repr a -> repr Bool

  pair :: repr a -> repr b -> repr (a, b)
  triple :: repr a -> repr b -> repr c -> repr (a, b, c)

fortytwo = int 42

-- In T-LINQ the second version, with "quoted" lambda is superior because it takes part in
-- normalisation. I assume the same is true here as well. How do I see that?

q1 :: Symantics repr => repr Int -> repr [Order]
q1 xoid = for orders $ (\o -> where' (equals (oid o) xoid) $ yield o)

q1_2 = q1 (int 2)

q1_lam :: Symantics repr => repr (Int -> [Order])
q1_lam = lam (\xoid -> for orders $ (\o -> where' (equals (oid o) xoid) $ yield o))

q1_2_lam = app q1_lam (int 2)

-- This is somewhat okay.
-- We are in Haskell, there are no records.
-- It's fine to declare a type before using it.
-- Unfortunately, we also need the `sale` function in the Symantics (or Schema).
-- We can't just use the constructor :/
-- This is one of the things that annoyed me in DSH.
data Sale = Sale Int String Int
  deriving Show
-- We could generate a schema statically from the actual database schema, but doing this for
-- results of ad-hoc queries is really annoying.

q2 :: Symantics repr => repr Order -> repr [Sale]
q2 o = for products $ (\p ->
       where' (equals (p_pid p) (o_pid o)) $
       yield (sale (p_pid p) (name p) (price p `mult` qty o)))

-- this ties the query to its evaluator
--q3' :: Symantics repr => repr Int -> repr [Sale]
q3' oid = map (\o -> eval (q2 (R o))) (eval (q1 oid))

compose :: Symantics repr => (t -> repr [a]) -> (repr a -> repr [b]) -> t -> repr [b]
compose q r x = for (q x) $ (\y -> r y)

q3 :: Symantics repr => repr Int -> repr [Sale]
q3 x = compose q1 q2 x

q2_lam :: Symantics repr => repr (Order -> [Sale])
q2_lam = lam (\o ->
       for products $ (\p ->
       where' (equals (p_pid p) (o_pid o)) $
       yield (sale (p_pid p) (name p) (price p `mult` qty o))))

compose_lam :: Symantics repr => repr ((a -> [a1]) -> (a1 -> [b]) -> a -> [b])
compose_lam = lam (\q -> lam (\r -> lam (\x ->
              for (app q x) $ (\y -> app r y))))

q3_lam :: Symantics repr => repr (Int -> [Sale])
q3_lam = app (app compose_lam q1_lam) q2_lam


-- Use tuples for result of q2. Not sure what's worse. They are both pretty bad...
q2_pair :: Symantics repr => repr (Order -> [(Int, String, Int)])
q2_pair = lam (\o ->
            for products $ (\p ->
            where' (equals (p_pid p) (o_pid o)) $
            yield (triple (p_pid p) (name p) (price p `mult` qty o))))

q3_pair :: Symantics repr => repr (Int -> [(Int, String, Int)])
q3_pair = app (app compose_lam q1_lam) q2_pair

data R a = R { eval :: a }

instance Symantics R where
  pair (R a) (R b) = R (a, b)
  triple (R a) (R b) (R c) = R (a, b, c)
  int = R
  for :: R [a] -> (R a -> R [b]) -> R [b]
  for tbl f = case tbl of
                R []     -> R []
                R (x:xs) -> R (eval (f (R x)) `mappend` (eval (for (R xs) f)))
  where' (R p) e = if p then e else R []
  yield (R x) = R [x]
  nil = R []
  equals (R a) (R b) = R (a == b)
  lam :: (R a -> R b) -> R (a -> b)
  lam f = R (\a -> eval (f (R a)))
  app :: R (a -> b) -> R a -> R b
  app (R f) (R a) = R (f a)
  mult (R a) (R b) = R (a * b)

  p_pid (R (Product pid _ _)) = R pid
  name (R (Product _ name _)) = R name
  price (R (Product _ _ price)) = R price
  products = R [Product 1 "Tablet" 500, Product 2 "Laptop" 1000, Product 3 "Desktop" 1000, Product 4 "Router" 150, Product 5 "HDD" 100, Product 6 "SSD" 500]

  oid (R (Order oid _ _)) = R oid
  o_pid (R (Order _ o_pid _)) = R o_pid
  qty (R (Order _ _ qty)) = R qty
  orders = R [Order 1 1 5, Order 1 2 5, Order 1 4 2, Order 2 5 10, Order 2 6 20, Order 3 2 50]

  sale (R a) (R b) (R c) = R (Sale a b c)

res_q1_2 = eval q1_2

res_q1_2_lam = eval q1_2_lam


data S a = S { toString :: String }

-- I don't think this is the way to do it.
-- Check the tagless final tutorial...
instance Symantics S where
  -- pair (S a) (S b) = S (a ++ ", " ++ b)
  for :: S [a] -> (S a -> S [b]) -> S [b]
  for (S tbls) f = let name = [head tbls] in S ("FOR (" ++ name ++ " <- " ++ tbls ++ ") " ++ toString (f (S name)))
  orders = S "orders"
  products = S "products"
  where' (S p) e = S ("WHERE " ++ p ++ " " ++ toString e)
  equals (S a) (S b) = S ("(" ++ a ++ " == " ++ b ++ ")")
  oid (S o) = S (o ++ ".oid")
  o_pid (S o) = S (o ++ ".pid")
  p_pid (S p) = S (p ++ ".pid")
  sale (S a) (S b) (S c) = S ("(Sale " ++ a ++ " " ++ b ++ " " ++ c ++ ")")
  name (S o) = S (o ++ ".name")
  price (S o) = S (o ++ ".price")
  qty (S o) = S (o ++ ".qty")
  mult (S a) (S b) = S ("(" ++ a ++ "*" ++ b ++ ")")
  int n = S (show n)
  yield (S a) = S ("YIELD " ++ a)
  -- app ? this is wrong...

s_q1_2 = toString q1_2

s_q3 = toString $ q3 (int 2)
s_q3_lam = toString $ app q3_lam (int 2)
