{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{- Werror=incomplete-patterns -}
module Lib
    ( someFunc
    ) where

import Ty (Ty)
import Supply (MonadSupply, fresh)
import qualified Ty as Ty
import Data.Bifunctor (second)
import Data.Monoid ((<>))
import Control.Monad (ap)
import Control.Exception (assert)
import GHC.Stack (HasCallStack)
import Text.PrettyPrint.ANSI.Leijen (dullgreen, vcat, indent, green, (<$$>), hang, char, blue, semiBraces, cat, punctuate, brackets, Doc, Pretty, bold, pretty, cyan, putDoc, displayS, renderPretty, (<+>), dot, text, parens)

lookup3 :: Eq a => a -> [(a, b, c)] -> Maybe (b, c)
lookup3 _ [] = Nothing
lookup3 a ((a', b, c):_) | a == a' = Just (b, c)
lookup3 a (_:xs) = lookup3 a xs

type V = Integer
type L = String

data C = CB Bool | CT String | CBottom
  deriving (Show)

data E
  = V V
  | C C
  | Fix V E
  | V :-> E
  | E :$ E
  | Ty.V :=> E
  | E :§ Ty
  | U [E]
  | For V E E
  | R [(L,E)]
  | E :. L
  | ITE E E E
  | L :@ E
  | E :| [(L,V,E)]
  | E ::: Ty
  | TyC Ty (E, E, E, (Ty.V, E), (Ty.V, E), (Ty.V, E))
  | Rmap E E
  | TrC E ((V, E), (V, E), (V, E), (Ty.V, V, E), (V, E)) --, (Ty.V, V, E))

instance Pretty E where
  pretty = prettyE False

pparens True = parens
pparens False = id

kw :: String -> Doc
kw = bold . text

prettyE :: Bool -> E -> Doc
prettyE _ (V v) = cyan (pretty v)
prettyE _ (C c) = text $ show c
prettyE p (Fix x e) = pparens p $ kw "fix" <+> pretty x <> dot <> pretty e
prettyE p (v :-> e) = pparens p $ kw "λ" <> pretty v <> dot <> pretty e
prettyE p (a :$ b) = pparens p $ prettyE True a <+> prettyE True b
prettyE p (v :=> e) = pparens p $ kw "Λ" <> pretty v <> dot <> pretty e
prettyE p (e :§ t) = pparens p $ prettyE True e <+> text (show t)
prettyE p (U []) = brackets mempty
prettyE _ (U [e]) = brackets (pretty e)
prettyE p (U es) = pparens p $ cat $ punctuate (kw " ++ ") (map pretty es)
prettyE p (For v i o) = pparens p $ hang 2 $ kw "for" <+> parens (pretty v <+> kw "<-" <+> pretty i) <$$> pretty o
prettyE _ (R fs) = semiBraces (map (\(l, e) -> blue (text l) <> char '=' <> pretty e) fs)
prettyE p (e :. l) = pparens p $ pretty e <> dot <> blue (text l)
prettyE p (ITE c t e) = pparens p $ kw "if" <+> pretty c <+> kw "then" <+> pretty t <+> kw "else" <+> pretty e
prettyE p (c :@ e) = pparens p $ dullgreen (text c) <+> prettyE True e
prettyE p (e :| cs) = pparens p $ kw "case" <+> pretty e <+> kw "of" <$$>
  indent 2 (vcat (map (\(l, v, c) -> dullgreen (text l) <+> pretty v <+> kw "=>" <+> pretty c) cs))
prettyE p (e ::: t) = pparens p $ pretty e <+> text "::" <+> text (show t)
prettyE p (Rmap a b) = pparens p $ kw "rmap" <+> prettyE True a <+> prettyE True b
prettyE p (TyC x (b, i, s, (lv, l), (rv, r), (tv, t))) = pparens p $ hang 2 $ kw "typecase" <+> text (show x) <+> kw "of" <$$>
  text "Bool" <+> kw "=>" <+> pretty b <$$>
  text "Int" <+> kw "=>" <+> pretty i <$$>
  text "String" <+> kw "=>" <+> pretty s <$$>
  text "List" <+> pretty lv <+> kw "=>" <+> pretty l <$$>
  text "Record" <+> pretty rv <+> kw "=>" <+> pretty r <$$>
  text "Trace" <+> pretty tv <+> kw "=>" <+> pretty t
prettyE p (TrC e ((lv, l), (itv, it), (iev, ie), (ft, fv, f), (rv, r))) = pparens p $ hang 2 $ kw "tracecase" <+> pretty e <+> kw "of" <$$>
  dullgreen (text "Lit") <+> pretty lv <+> kw "=>" <+> pretty l <$$>
  dullgreen (text "IfThen") <+> pretty itv <+> kw "=>" <+> pretty it <$$>
  dullgreen (text "IfElse") <+> pretty iev <+> kw "=>" <+> pretty ie <$$>
  dullgreen (text "For") <+> pretty ft <+> pretty fv <+> kw "=>" <+> pretty f <$$>
  dullgreen (text "Row") <+> pretty rv <+> kw "=>" <+> pretty r

instance Show E where
  showsPrec _ e = displayS (renderPretty 0.4 90 (pretty e))

newtype Env = Env [(V, Either E Ty)]
  deriving Show

lookupE :: HasCallStack => V -> Env -> E
lookupE v (Env l) = case lookup v l of
  Nothing -> error $ "Unbound variable " ++ show v
  Just (Left e) -> e
  Just (Right _) -> error "Not an expression but a type"

lookupTy :: V -> Env -> Ty
lookupTy v (Env l) = case lookup v l of
  Nothing -> error $ "Unbound variable " ++ show v
  Just (Left _) -> error "Not a type but an expression"
  Just (Right t) -> t

bindE :: V -> E -> Env -> Env
bindE v e (Env l) = Env $ (v,Left e):l

bindTy :: V -> Ty -> Env -> Env
bindTy v t (Env l) = Env $ (v,Right t):l

subst :: E -> (V, E) -> E
subst (V v) (v', e) | v == v' = e
subst (V v) _ = V v
subst (C c) _ = C c
subst (x :-> b) s = x :-> (b `subst` s)
subst (a :$ b) s = (a `subst` s) :$ (b `subst` s)
subst (x :=> b) s = x :=> (b `subst` s)
subst (a :§ t) s = (a `subst` s) :§ t
subst (For x i o) s = For x (i `subst` s) (o `subst` s)
subst (U l) s = U (flip subst s <$> l)
subst (l :@ e) s = l :@ (e `subst` s)
subst (e :| cs) s = (e `subst` s) :| map (\(l,v,c) -> (l,v,c `subst` s)) cs
subst (e :. l) s = (e `subst` s) :. l
subst (Rmap a b) s = Rmap (a `subst` s) (b `subst` s)
subst (TyC x (b, i, s, (lv, l), (rv, r), (tv, t))) sub = TyC x
  (b `subst` sub,
   i `subst` sub,
   s `subst` sub,
   (lv, l `subst` sub),
   (rv, r `subst` sub),
   (tv, t `subst` sub))
subst (TrC e ((lv, l), (itv, it), (iev, ie), (ft, fv, f), (rv, r))) s = TrC (e `subst` s)
  ((lv, l `subst` s),
   (itv, it `subst` s),
   (iev, ie `subst` s),
   (ft, fv, f `subst` s),
   (rv, r `subst` s))
subst e _ = error $ "missing case in subst: " <> show e

substT :: E -> (Ty.V, Ty) -> E
substT (V v) (v',_) = assert (v /= v') $ V v
substT (C c) _ = C c
substT (TyC x (b, i, s, (lv, l), (rv, r), (tv, t))) rep = TyC (x `Ty.subst` rep)
  (b `substT` rep,
   i `substT` rep,
   s `substT` rep,
   (lv, l `substT` rep),
   (rv, r `substT` rep),
   (tv, t `substT` rep))
substT (x :-> b) s = x :-> (b `substT` s)
substT (For x i o) s = For x (i `substT` s) (o `substT` s)
substT (U l) s = U (flip substT s <$> l)
substT (a :$ b) s = (a `substT` s) :$ (b `substT` s)
substT (x :=> b) s = x :=> (b `substT` s)
substT (a :§ t) s = (a `substT` s) :§ (t `Ty.subst` s)
substT (Rmap a b) s = Rmap (a `substT` s) (b `substT` s)
substT (TrC e ((lv, l), (itv, it), (iev, ie), (ft, fv, f), (rv, r))) s = TrC (e `substT` s)
  ((lv, l `substT` s),
   (itv, it `substT` s),
   (iev, ie `substT` s),
   (ft, fv, f `substT` s),
   (rv, r `substT` s))
substT (e :. l) s = e `substT` s :. l
substT (l :@ e) s = l :@ (e `substT` s)
substT e _ = error $ "missing case in substT: " <> show e

one :: HasCallStack => E -> E
one (V v) = V v
one (C c) = C c
one (U ls) = U (one <$> ls) -- okay, fine, this does multiple steps... 
one ((x :-> b) :$ a) = b `subst` (x, a)
one (a :$ b) = one a :$ b
one ((a :=> b) :§ t) = b `substT` (a, t)
one (a :§ t) = one a :§ t
one (TyC x (b, i, s, (lv, l), (rv, r), (tv, t))) = case Ty.norm x of
  Ty.B -> b
  Ty.L e -> l `substT` (lv, e)
one (For x (U []) _) = U []
one (For x (U [i]) o) = o `subst` (x, i)
one (For x i o) = For x (one i) (one o) -- again, it's too hard to keep track of what we've done already
one e = error $ show e

symN n e = iterate one e !! n

sym :: HasCallStack => Env -> E -> E
sym env (V v) = lookupE v env
sym _env (C c) = C c
sym env (U ls) = U (map (sym env) ls)
sym env ((x :-> b) :$ a) = sym (bindE x (sym env a) env) b
sym env (a :$ b) = sym env $ (sym env a) :$ b
sym env (For x i o) = f x (sym env i) o
  where f x (U []) _ = U []
        f x (U [i]) o = sym (bindE x i env) o
        f x (U is) o = sym env $ U (map (\i -> For x i o) is)
        f x (C (CT t)) o = For x (C (CT t)) (sym (bindE x (V x) env) o)
        f x (For y l m) n = sym env (For y l (For x m n))
        -- f _ e _ = error $ show e
sym env (R fs) = R (map (second (sym env)) fs)
sym env (r :. l) = p (sym env r)
  where p (R fs) = case lookup l fs of
          Nothing -> error "Label not present"
          Just e -> sym env e
        p (V x) = V x :. l -- If we eta-expanded for-bound variables we would not need this, right?
        p (ITE i t e) = sym env $ ITE i (p t) (p e)
sym env (ITE i t e) = ite (sym env i) t e
  where ite (C (CB True)) t _ = sym env t
        ite (C (CB False)) _ e = sym env e
        ite i t e = ITE i (sym env t) (sym env e)
sym env (e :| cases) = c (sym env e)
  where c (l :@ v) = case lookup3 l cases of
          Nothing -> error "No matching case"
          Just (x, b) -> sym (bindE x v env) b
-- sym env (Fix x e) = sym (bindE x (Fix x e) env) e -- Dangerous!
sym env ((a :=> b) :§ t) = sym (bindTy a (tySym env t) env) b -- we should probably normalize types
sym env (a :§ t) = sym env $ sym env a :§ t
sym _env f@(_ :-> _) = error $ "unexpected function " ++ show f
sym _env tf@(_ :=> _) = error $ "unexpected type function: " ++ show tf
sym _env (_ :@ _) = error "unexpected variant constructor"
sym env tyc@(TyC thetype (b, i, s, (ltv, lb), _, _)) = case tySym env thetype of
  Ty.B -> sym env b
  Ty.L ety -> sym (bindTy ltv ety env) lb
  -- el -> error $ show el
-- sym env e = error $ show e

tySym :: HasCallStack => Env -> Ty -> Ty
tySym env (Ty.V x) = lookupTy x env
tySym env Ty.B = Ty.B
tySym env ((alpha Ty.:-> body) Ty.:$ arg) = tySym (bindTy alpha (tySym env arg) env) body
tySym env (tf Ty.:$ arg) = tySym env $ tySym env tf Ty.:$ arg
tySym env (Ty.Rec a cases@(b, i, s, l, r, t)) = case tySym env a of
  Ty.B -> tySym env b
  Ty.L x -> tySym env $ l Ty.:$ x Ty.:$ Ty.Rec x cases
tySym env (v Ty.:-> body) = v Ty.:-> tySym (bindTy v (Ty.V v) env) body
tySym env (Ty.L t) = Ty.L (tySym env t)
tySym env (Ty.T t) = Ty.T (tySym env t)
-- tySym _env e = error $ show e

spec :: [(V, E)] -> Integer -> E -> E
spec fenv 0 (Fix _ _) = C CBottom
spec fenv n (Fix x e) = spec ((x,e):fenv) (n-1) e
spec fenv n (V v) = case lookup v fenv of
  Nothing -> V v
  Just _ | n == 0 -> C CBottom
  Just fixbody -> spec fenv (n-1) fixbody
spec _ _ (C c) = C c
spec fenv n (x :-> b) = x :-> spec fenv n b
spec fenv n (a :$ b) = spec fenv n a :$ spec fenv n b
spec fenv n (x :=> b) = x :=> spec fenv n b
spec fenv n (a :§ t) = spec fenv n a :§ t
spec fenv n (U l) = U (map (spec fenv n) l)
spec fenv n (For x i o) = For x (spec fenv n i) (spec fenv n o)
spec fenv n (R l) = R (map (second (spec fenv n)) l)
spec fenv n (r :. f) = spec fenv n r :. f
spec fenv n (ITE c t e) = ITE (spec fenv n c) (spec fenv n t) (spec fenv n e)
spec fenv n (l :@ e) = l :@ spec fenv n e
spec fenv n (e :| cs) = spec fenv n e :| map (\(l, v, c) -> (l, v, spec fenv n c)) cs
spec fenv n (e ::: t) = spec fenv n e ::: t
spec fenv n (TyC x (b, i, s, (lv, l), (rv, r), (tv, t))) = TyC x
  (spec fenv n b,
   spec fenv n i,
   spec fenv n s,
   (lv, spec fenv n l),
   (rv, spec fenv n r),
   (tv, spec fenv n t))
spec fenv n (Rmap f r) = Rmap (spec fenv n f) (spec fenv n r)
spec fenv n (TrC e ((lv, l), (itv, it), (iev, ie), (ft, fv, f), (rv, r))) = TrC (spec fenv n e)
  ((lv, spec fenv n l),
   (itv, spec fenv n it),
   (iev, spec fenv n ie),
   (ft, fv, spec fenv n f),
   (rv, spec fenv n r))

trace :: MonadSupply V m => E -> m E
trace (V x) = error $ "unannotated variable " ++ show x
trace (V x ::: t) = fresh >>= \k -> pure $
  k :-> (V k :§ t :$ V x)
trace (C (CB b)) = fresh >>= \k -> pure $
  k :-> (V k :§ Ty.B :$ ("Lit" :@ C (CB b)))
trace (U ls) = fresh >>= \k -> do
  ls' <- traverse (\l -> do l' <- trace l; pure $ l' :$ V k) ls
  pure $ k :-> U ls'

newtype M a = M (V -> (V, a))

instance Functor M where
  fmap f (M a) = M (\v -> f <$> a v)

instance Applicative M where
  pure a = M (\v -> (v, a))
  (<*>) = ap

instance Monad M where
  M a >>= amb = M (\v -> case a v of (v', a') -> case amb a' of M b -> b v')

peek :: M V
peek = M (\v -> (v, v))

reset :: V -> M ()
reset v = M (const (v, ()))

instance MonadSupply Integer M where
  fresh = do
    v <- peek
    reset (v + 1)
    pure v

evalSupply :: V -> M a -> a
evalSupply v (M a) = snd (a v)

value :: M E
value = do
  value <- fresh
  a <- fresh
  xb <- fresh
  xi <- fresh
  xs <- fresh
  b <- fresh
  xl <- fresh
  y <- fresh
  r <- fresh
  xr <- fresh
  c <- fresh
  xt <- fresh
  lit <- fresh
  it <- fresh
  ie <- fresh
  d <- fresh
  f <- fresh
  tr <- fresh
  pure $ Fix value $ a :=>
    (TyC (Ty.V a)
     (xb :-> V xb, xi :-> V xi, xs :-> V xs,
      (b, xl :-> For y (V xl) (U [V value :§ Ty.V b :$ V y])),
      (r, xr :-> Rmap (V value) (V xr)),
      (c, xt :-> TrC (V xt)
        ((lit, V lit),
         (it, V value :§ Ty.T (Ty.V c) :$ (V it :. "then")),
         (ie, V value :§ Ty.T (Ty.V c) :$ (V ie :. "else")),
         (d, f, V value :§ Ty.T (Ty.V c) :$ (V f :. "out")),
         (tr, V tr :. "data")))))

someFunc :: IO ()
someFunc = do
  -- let sym' = sym (Env [])
  -- putStrLn $ show $ sym' $ (1 :-> V 1) :$ C (CB True)
  -- putStrLn $ show $ sym' $ (U [C (CB True)])
  -- putStrLn $ show $ sym' $ (For 1 (U [C (CB True)]) (U [V 1]))
  -- putStrLn $ show $ sym' $ (For 1 (U [R [("a", C (CB True))]]) (U [V 1 :. "a"]))
  -- putStrLn $ show $ sym' $ (For 1 (U [R [("a", C (CB True))]]) (U [ITE (V 1 :. "a") (C (CB False)) (C (CB True))]))
  -- putStrLn $ show $ sym' $ (For 1 (U [R [("a", C (CB True))]]) (U [(ITE (V 1 :. "a") (V 1) (R [("a", C (CB False))])) :. "a"]))
  -- putStrLn $ show $ sym' $ For 1 (C (CT "agencies")) (U [V 1])
  -- putStrLn $ show $ sym' $ For 1 (C (CT "agencies")) (For 2 (C (CT "tours")) (U [R [("a", V 1), ("t", V 2)]]))
  -- putStrLn $ show $ sym' $ For 1 (C (CT "agencies")) (U [V 1 :. "name"])
  -- putStrLn $ show $ sym' $ For 1 (C (CT "tbl")) (U [(ITE (V 1 :. "a") (V 1) (R [("a", C (CB False))])) :. "a"])
  -- putStrLn $ show $ valueOfTraceOfSomething
  -- -- putStrLn $ show $ sym' $ valueOfTraceOfSomething
  -- -- let foo = Fix 0 (V 5 :$ V 0 :$ V 6)
  -- -- let bar = Fix 1 (V 7 :$ V 1 :$ V 8 :$ foo :$ V 9)
  -- -- putStrLn $ show $ foo
  -- -- putStrLn $ show $ spec [] 0 foo
  -- -- putStrLn $ show $ spec [] 1 foo
  -- -- putStrLn $ show $ spec [] 2 foo
  -- -- putStrLn $ show $ spec [] 3 foo
  -- -- putStrLn $ show $ bar
  -- -- putStrLn $ show $ spec [] 0 bar
  -- -- putStrLn $ show $ spec [] 1 bar
  -- -- putStrLn $ show $ spec [] 2 bar
  -- -- putStrLn $ show $ spec [] 3 bar
  -- putStrLn $ show $ spec [] 1 $ valueOfTraceOfSomething
  -- putStrLn $ show $ sym' $ spec [] 1 $ valueOfTraceOfSomething
  let valueOfTraceOfSomething = evalSupply 100 $ do
        t <- trace (U [C (CB True)])
        x <- fresh
        a <- fresh
        v <- value
        tRACE <- Ty.tRACE
        pure $ v :§ (tRACE Ty.:$ Ty.L Ty.B) :$ (t :$ (a :=> (x :-> V x)))
  putStrLn $ show $ spec [] 3 $ valueOfTraceOfSomething
  putStrLn $ show $ symN 0 $ spec [] 1 $ valueOfTraceOfSomething
  -- putStrLn $ show $ symN 6 $ spec [] 2 $ valueOfTraceOfSomething
  -- putStrLn $ show $ symN 7 $ spec [] 2 $ valueOfTraceOfSomething
  -- putStrLn $ show $ symN 8 $ spec [] 2 $ valueOfTraceOfSomething
  -- putStrLn $ show $ symN 9 $ spec [] 2 $ valueOfTraceOfSomething
  -- putStrLn $ show $ symN 10 $ spec [] 2 $ valueOfTraceOfSomething
