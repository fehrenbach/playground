{-# LANGUAGE InstanceSigs, FlexibleContexts, DeriveFunctor, StandaloneDeriving, TemplateHaskell, RankNTypes, ScopedTypeVariables #-}

module Lib
    ( someFunc
    , clam
    , elam
    , etlam
    ) where

import Bound ((>>>=), Var(B,F))
import Bound.Scope.Simple
import Control.Monad (ap)
import Control.Monad.Morph (lift)
-- import Data.Functor.Classes (Eq1)
import Data.Deriving (deriveEq1)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import qualified Text.PrettyPrint.ANSI.Leijen as P

-- I'm sure there's a better way to do this, but my hoogle-fu is insufficient
mapSnd :: (a -> b) -> [(l, a)] -> [(l, b)]
mapSnd _ [] = []
mapSnd f ((a,b):r) = (a, f b) : mapSnd f r

pparens :: Bool -> Doc -> Doc
pparens True d = black (char '(') <> d <> black (char ')')
pparens False d = d

tvars, evars :: [String]
tvars = ["α", "β", "γ"] <> [ "α" <> show x | x <- [0 :: Integer ..] ]
evars = ["x", "y", "z"] <> [ "x" <> show x | x <- [0 :: Integer ..] ]

data Kind = KType | KArrow Kind Kind
  deriving (Eq)

prettyKind :: Kind -> Doc
prettyKind KType = text "Type"
prettyKind (KArrow l r) = parens $ prettyKind l <+> text "->" <+> prettyKind r 

type Label = String

data Constructor a
  = CBool
  | CVar a {- Uhm. I'd quite like a type annotation on variables, but then how do I write `return`?! -}
  | CLambda Kind (Scope () Constructor a)
  | CApp (Constructor a) (Constructor a)
  | CList (Constructor a)
  | CTrace (Constructor a)
  -- I don't really want another datatype
  -- | CRowNil
  -- | CRowCons Label (Constructor a) (Constructor a)
  deriving (Functor)

deriveEq1 ''Constructor

instance Applicative Constructor where
  pure = return
  (<*>) = ap

instance Monad Constructor where
  return = CVar

  CBool >>= _ = CBool
  CVar a >>= f = f a
  CLambda k b >>= f = CLambda k (b >>>= f)
  CApp a b >>= f = CApp (a >>= f) (b >>= f)
  CList a >>= f = CList (a >>= f)
  CTrace a >>= f = CTrace (a >>= f)
  -- CRowNil >>= _ = CRowNil
  -- CRowCons l c r >>= f = CRowCons l (c >>= f) (r >>= f)

clam :: Eq a => a -> Kind -> Constructor a -> Constructor a
clam a k b = CLambda k (abstract1 a b)

prettyConstructor :: [String] -> Bool -> Constructor String -> Doc
prettyConstructor [] _ _ = error "ran out of type variables during constructor pretty printing"
prettyConstructor _ _ CBool = text "Bool*"
prettyConstructor _ _ (CVar a) = text a
prettyConstructor (av:avs) p (CLambda k body) = pparens p $
  char 'λ' <> text av <> char ':' <> prettyKind k <> char '.' <> prettyConstructor avs False (instantiate1 (CVar av) body)
prettyConstructor avs p (CApp a b) = pparens p $
  prettyConstructor avs True a <+> prettyConstructor avs True b
prettyConstructor avs p (CList a) = pparens p $ text "List*" <+> prettyConstructor avs True a
prettyConstructor avs p (CTrace a) = pparens p $ text "Trace*" <+> prettyConstructor avs True a

data Type c a
  = TBool
  | TT (c a)
  -- the body is a type with an additional bound constructor variable
  | TForall Kind (Type (Scope () c) a)
  | TArrow (Type c a) (Type c a)
  | TList (Type c a)
  | TTrace (Type c a)
  deriving (Functor)

deriveEq1 ''Type

tforall :: Eq a => a -> Kind -> Type Constructor a -> Type Constructor a
tforall a k body = TForall k (tAbstract1 a body)

tAbstract1 :: Functor constructor => Eq a => a -> Type constructor a -> Type (Scope () constructor) a
tAbstract1 = go abstract1
  where
    go :: forall c c' a. Eq a
       => (forall v. Eq v => v -> c v -> c' v)
      -> a -> Type c a -> Type c' a
    go _ _ TBool = TBool
    go f a (TT c) = TT (f a c)
    go f a (TForall k b) = TForall k (go f' a b)
      where
        f' v = Scope . f (F v) . unscope
    go f a (TArrow l r) = TArrow (go f a l) (go f a r)
    go f a (TList t) = TList (go f a t)
    go f a (TTrace t) = TTrace (go f a t)

prettyType :: [String] -> Bool -> Type Constructor String -> Doc
prettyType [] _ _ = error "ran out of type variables during type pretty printing"
prettyType _ _ TBool = text "Bool"
prettyType avs _ (TT c) = char 'T' <> parens (prettyConstructor avs False c)
prettyType (av:avs) p (TForall k body) = pparens p $
  char '∀' <> text av <> kindAnnotation <> char '.' <> prettyType avs p (tInstantiate1 (CVar av) body)
  where kindAnnotation = case k of
          KType -> empty
          _ -> char ':' <> prettyKind k
prettyType avs p (TArrow a b) = pparens p $ prettyType avs True a <+> text "->" <+> prettyType avs True b
prettyType avs p (TList a) = pparens p $ text "List" <+> prettyType avs True a
prettyType avs p (TTrace a) = pparens p $ text "Trace" <+> prettyType avs True a

tInstantiate1 :: forall operand b a.
  (Applicative operand, Monad operand) =>
  operand a -> Type (Scope b operand) a -> Type operand a
tInstantiate1 = go instantiate1
  where
    go :: forall o o' u. (forall v. operand v -> o v -> o' v) -> operand u -> Type o u -> Type o' u
    go _ _ TBool = TBool
    go f a (TT c) = TT (f a c)
    go f a (TForall k b) = TForall k (go f' a b)
      where
        f' v = Scope . f (fmap F v) . unscope
    go f a (TArrow l r) = TArrow (go f a l) (go f a r)
    go f a (TList t) = TList (go f a t)
    go f a (TTrace t) = TTrace (go f a t)

data Expr c a x
  = ETrue
  | EVar x
  | EIf (Expr c a x) (Expr c a x) (Expr c a x)
  | ELam (Type c a) (Scope () (Expr c a) x)
  | EApp (Expr c a x) (Expr c a x)
  | ETLam Kind (Expr (Scope () c) a x)
  | ETApp (Expr c a x) (c a)
  | EVariant Label (Expr c a x) -- add type hint?
  | EEmptyList -- add type hint? (Type c a)
  | ESingletonList (Expr c a x)
  | EConcat (Expr c a x) (Expr c a x)
  -- The Type is the type of ELEMENTS of the first Expr argument
  | EFor (Type c a) (Expr c a x) (Scope () (Expr c a) x)
  | ERecord [(Label, Expr c a x)]
  deriving (Functor)

instance (Eq a, Monad c) => Applicative (Expr c a) where
  pure = return
  (<*>) = ap

instance (Eq a, Monad c) => Monad (Expr c a) where
  return = EVar

  ETrue >>= _ = ETrue
  EVar x >>= f = f x
  ELam t b >>= f = ELam t (b >>>= f)
  EFor t e b >>= f = EFor t (e >>= f) (b >>>= f)
  EApp l r >>= f = EApp (l >>= f) (r >>= f)
  ETLam k b >>= f = ETLam k (b >>= liftCE . f)
  ETApp e c >>= f = ETApp (e >>= f) c
  EVariant l e >>= f = EVariant l (e >>= f)
  EEmptyList >>= _ = EEmptyList
  ESingletonList e >>= f = ESingletonList (e >>= f)
  EConcat l r >>= f = EConcat (l >>= f) (r >>= f)
  ERecord le >>= f = ERecord (map (\(l, x) -> (l, x >>= f)) le)
  EIf i t e >>= f = EIf (i >>= f) (t >>= f) (e >>= f)

liftCE :: Monad c => Expr c a b -> Expr (Scope () c) a b
liftCE ETrue = ETrue
liftCE (EVar x) = EVar x
liftCE (ELam t b) = ELam (liftCT t) (hoistScope liftCE b)
liftCE (EFor t e b) = EFor (liftCT t) (liftCE e) (hoistScope liftCE b)
liftCE (EApp l r) = EApp (liftCE l) (liftCE r)
liftCE (ETLam k b) = ETLam k (liftCE b)
liftCE (ETApp e c) = ETApp (liftCE e) (lift c)
liftCE (EVariant l e) = EVariant l (liftCE e)
liftCE EEmptyList = EEmptyList
liftCE (ESingletonList e) = ESingletonList (liftCE e)
liftCE (EConcat l r) = EConcat (liftCE l) (liftCE r)
liftCE (EIf i t e) = EIf (liftCE i) (liftCE t) (liftCE e)
liftCE (ERecord l) = ERecord (mapSnd liftCE l)

liftCT :: Monad c => Type c a -> Type (Scope () c) a
liftCT TBool = TBool
liftCT (TT c) = TT (lift c)
liftCT (TForall k c) = TForall k (liftCT c)
liftCT (TArrow a b) = TArrow (liftCT a) (liftCT b)
liftCT (TList a) = TList (liftCT a)
liftCT (TTrace a) = TTrace (liftCT a)

elam :: Eq x => x -> Type c a -> Expr c a x -> Expr c a x
elam x t b = ELam t (abstract1 x b)

efor :: Eq x => x -> Type c a -> Expr c a x -> Expr c a x -> Expr c a x
efor x t i o = EFor t i (abstract1 x o)

-- instantiate a constructor in an expression
eInstantiateC1 :: Eq a => Monad c => c a -> Expr (Scope () c) a x -> Expr c a x
eInstantiateC1 _ ETrue = ETrue
eInstantiateC1 _ (EVar x) = EVar x
eInstantiateC1 a (ELam t b) = ELam (tInstantiate1 a t) (hoistScope (eInstantiateC1 a) b)
eInstantiateC1 a (EApp l r) = EApp (eInstantiateC1 a l) (eInstantiateC1 a r)
eInstantiateC1 a (ETLam k b) = ETLam k (eInstantiateC1 (lift a) b)
eInstantiateC1 a (ETApp e c) = ETApp (eInstantiateC1 a e) (instantiate1 a c)
eInstantiateC1 _ EEmptyList = EEmptyList
eInstantiateC1 a (EVariant l e) = EVariant l (eInstantiateC1 a e)
eInstantiateC1 a (ESingletonList e) = ESingletonList (eInstantiateC1 a e)
eInstantiateC1 a (EConcat l r) = EConcat (eInstantiateC1 a l) (eInstantiateC1 a r)
eInstantiateC1 a (EFor t i o) = EFor (tInstantiate1 a t) (eInstantiateC1 a i) (hoistScope (eInstantiateC1 a) o)
eInstantiateC1 a (EIf c t e) = EIf (eInstantiateC1 a c) (eInstantiateC1 a t) (eInstantiateC1 a e)
eInstantiateC1 a (ERecord l) = ERecord (mapSnd (eInstantiateC1 a) l)

-- abstract over a constructor in an expression
eAbstractC1 :: Eq a => Functor c => a -> Expr c a x -> Expr (Scope () c) a x
eAbstractC1 _ ETrue = ETrue
eAbstractC1 _ (EVar x) = EVar x
eAbstractC1 a (ELam t b) = ELam (tAbstract1 a t) (hoistScope (eAbstractC1 a) b)
eAbstractC1 a (EApp l r) = EApp (eAbstractC1 a l) (eAbstractC1 a r)
eAbstractC1 a (ETLam k b) = ETLam k (eAbstractC1 a b)
eAbstractC1 a (ETApp e c) = ETApp (eAbstractC1 a e) (abstract1 a c)
eAbstractC1 _ EEmptyList = EEmptyList
eAbstractC1 a (EVariant l e) = EVariant l (eAbstractC1 a e)
eAbstractC1 a (ESingletonList e) = ESingletonList (eAbstractC1 a e)
eAbstractC1 a (EConcat l r) = EConcat (eAbstractC1 a l) (eAbstractC1 a r)
eAbstractC1 a (EFor t i o) = EFor (tAbstract1 a t) (eAbstractC1 a i) (hoistScope (eAbstractC1 a) o)
eAbstractC1 a (EIf c t e) = EIf (eAbstractC1 a c) (eAbstractC1 a t) (eAbstractC1 a e)
eAbstractC1 a (ERecord l) = ERecord (mapSnd (eAbstractC1 a) l)

etlam :: Eq a => Monad c => a -> Kind -> Expr c a x -> Expr c a x
etlam a k b = ETLam k (eAbstractC1 a b) -- this should be actual abstract, not my misnamed one, I think

-- polyId' :: Expr Constructor String String
-- polyId' = etlam "a" KType (elam "ex" (TT (CVar "a")) (EVar "ex"))

polyId :: Expr Constructor a x
polyId = ETLam KType $ ELam (TT $ toScope (CVar (B ()))) $ toScope (EVar (B ()))

traceId :: Constructor a -> Expr Constructor a x
traceId tracetf = ETLam KType $ ELam (TT $ toScope (CApp (F <$> tracetf) (CVar (B ())))) $ toScope (EVar (B ()))

isApp :: Expr c a x -> Bool
isApp (EApp _ _) = True
isApp (ETApp _ _) = True
isApp _ = False

prettyExpr :: ([String], [String]) -> Bool -> Expr Constructor String String -> Doc
prettyExpr ([], _) _ _ = error "ran out of variable names"
prettyExpr (_, []) _ _ = error "ran out of type variable names"
prettyExpr _ _ ETrue = text "true"
prettyExpr _ _ (EVar x) = text x
prettyExpr (v:vs, tvs) p (ELam t b) = pparens p $ hang 2 $ group $
  char 'λ' <> text v <> char ':' <> prettyType tvs False t <> char '.' P.<$$> prettyExpr (vs, tvs) False (instantiate1 (EVar v) b)
prettyExpr (vs, tv:tvs) p (ETLam k b) = pparens p $ hang 2 $ group $
  char 'Λ' <> text tv <> kindAnnotation <> char '.' P.<$$> prettyExpr (vs, tvs) False (eInstantiateC1 (CVar tv) b)
  where kindAnnotation = case k of
          KType -> empty
          _ -> char ':' <> prettyKind k
prettyExpr ns p (EVariant l e) = pparens p $
  dullgreen (text l) <+> prettyExpr ns True e
prettyExpr ns p (EApp l r) = pparens p $
  prettyExpr ns (not $ isApp l) l </> prettyExpr ns True r
prettyExpr (vs, tvs) p (ETApp e c) = pparens p $
  prettyExpr (vs, tvs) (not $ isApp e) e </> prettyConstructor tvs True c
prettyExpr _ _ EEmptyList = text "[]"
prettyExpr ns _ (ESingletonList e) = brackets $ prettyExpr ns False e
prettyExpr ns p (EConcat l r) = pparens p $ prettyExpr ns True l <+> text "++" <+> prettyExpr ns True r
prettyExpr (v:vs, tvs) p (EFor t i o) = pparens p $ hang 2 $
  bold (text "for") <+> parens (text v <> typeAnnotation <+> text "<-" <+> prettyExpr (v:vs, tvs) False i) P.<$> prettyExpr (vs, tvs) False (instantiate1 (EVar v) o)
  where typeAnnotation = char ':' <+> prettyType tvs False t
prettyExpr _ _ (ERecord []) = braces empty
prettyExpr ns _ (ERecord l) = group $ char '{' <> (align $ printRec ns l)
prettyExpr ns p (EIf c t e) = pparens p $ group $
  bold (text "if") <+> prettyExpr ns False c P.<$>
  bold (text "then") <+> prettyExpr ns False t P.<$>
  bold (text "else") <+> prettyExpr ns False e

printRec :: ([String], [String]) -> [(String, Expr Constructor String String)] -> Doc
printRec _ [] = char '}'
printRec ns [(l,x)] = blue (text l) <+> char '=' <+> prettyExpr ns False x <> char '}'
printRec ns ((l,x):r) = blue (text l) <+> char '=' <+> prettyExpr ns False x <> char ',' </> printRec ns r
{-

-- deriveShow1 ''Type
-- instance Show a => Show (Type a) where showsPrec = showsPrec1


-- bitraverse?
-- freeVariables :: Expr (Type String) String -> [String]
-- freeVariables = bitraverse
-}

betaReduce :: Eq a => Monad c => Expr c a x -> Expr c a x
betaReduce ETrue = ETrue
-- TODO might want to check types before reducing
betaReduce (EApp (ELam _t b) x) = instantiate1 x b
betaReduce (EApp f x) = EApp (betaReduce f) (betaReduce x)
-- TODO might want to check kinds before reducing
betaReduce (ETApp (ETLam _k b) c) = eInstantiateC1 c b
betaReduce (ETApp e c) = ETApp (betaReduce e) c
betaReduce (EVar x) = EVar x
betaReduce (ELam t b) = ELam t (hoistScope betaReduce b)
betaReduce (ETLam k b) = ETLam k (betaReduce b)
betaReduce (EVariant l e) = EVariant l (betaReduce e)
betaReduce (ESingletonList e) = ESingletonList (betaReduce e)
betaReduce EEmptyList = EEmptyList
betaReduce (EConcat l r) = EConcat (betaReduce l) (betaReduce r)
betaReduce (EFor t i o) = EFor t (betaReduce i) (hoistScope betaReduce o)
betaReduce (EIf c t e) = EIf (betaReduce c) (betaReduce t) (betaReduce e)
betaReduce (ERecord l) = ERecord (mapSnd betaReduce l)

betaReduceN :: Eq a => Monad c => Int -> Expr c a x -> Expr c a x
betaReduceN 0 e = e
betaReduceN n e = betaReduceN (n-1) (betaReduce e)


-- ttype :: Constructor String -> Type Constructor String
-- ttype c = TArrow (TT (CApp (CVar "TRACE") c)) (TT (CApp (CVar "TRACE") c))

ttype :: Constructor a -> Type Constructor a
ttype tracetf = TForall KType $
  TArrow (TT $ toScope $ CApp (fmap F tracetf) (CVar (B ())))
         (TT $ toScope $ CApp (fmap F tracetf) (CVar (B ())))

trace' :: Constructor a -> x -> Type Constructor a -> Expr Constructor a x -> Expr Constructor a x
trace' _ _ _ (ELam _ _) = error "cannot trace lambda"
trace' _ _ _ (ETLam _ _) = error "cannot trace Lambda"
trace' _ _ _ (EApp _ _) = error "cannot trace app"
trace' _ _ _ (EVariant _ _) = error "cannot trace variant constructor"
trace' tracetf _ (TT CBool) ETrue = ELam (ttype tracetf) $ toScope $
  EApp (ETApp (EVar (B ())) CBool) (EVariant "Lit" ETrue)
trace' tracetf _ (TT c) (EVar x) = ELam (ttype tracetf) $ toScope (EApp (ETApp (EVar (B ())) c) (EVar (F x)))
trace' tracetf _ _ EEmptyList = ELam (ttype tracetf) $ toScope $ EEmptyList
trace' tracetf value (TT (CList c)) (ESingletonList e) = ELam (ttype tracetf) $ toScope $
  ESingletonList (EApp (fmap F (trace' tracetf value (TT c) e)) (EVar (B ())))
trace' tracetf value t@(TT (CList c)) (EConcat l r) = ELam (ttype tracetf) $ toScope $
  EConcat (EFor (TT (CApp tracetf c)) (EApp (fmap F $ trace' tracetf value t l) (EVar (B ()))) $ toScope $
                (ESingletonList (EVar (B ()))))
          (EFor (TT (CApp tracetf c)) (EApp (fmap F $ trace' tracetf value t r) (EVar (B ()))) $ toScope $
                (ESingletonList (EVar (B ()))))
trace' tracetf value ct (ERecord l) = ELam ct $ toScope $
  ERecord (mapSnd (\x -> EApp (fmap F $ trace' tracetf value ct x) (EVar (B ()))) l)
trace' tracetf value (TT (CList nElementC)) (EFor (TT mElementC) m n) = ELam (ttype tracetf) $ toScope $
  EFor (TT (CApp tracetf mElementC))
       (EApp (fmap F (trace' tracetf value (TT (CList mElementC)) m)) (traceId tracetf)) $ toScope $
  -- Right, so this fmap is where we keep the "same" variable that was
  -- bound in the body before.
    EApp (fmap (\v -> case v of F x -> F (F x); B () -> B ()) (trace' tracetf (F value) (TT (CList nElementC)) (fromScope n))) $
         ETLam KType $ ELam (TT (toScope (CApp (F <$> tracetf) (CVar (B ()))))) $ toScope $
            EApp (ETApp (EVar (F (F (B ())))) (toScope (CTrace (CVar (B ())))))
                 (EVariant "For" (ERecord [("in", EVar (F (B ()))), ("out", EVar (B ()))]))
trace' tracetf value (TT c) (EIf eCond eThen eElse) = ELam (ttype tracetf) $ toScope $
  EIf (EApp (EVar (F value)) (tCondId F))
      (EApp (F <$> trace' tracetf value (TT c) eThen)
            (ETLam KType $ ELam (TT (toScope (CApp (F <$> tracetf) (CVar (B ()))))) $ toScope $
               EApp (ETApp (EVar (F (B ()))) (toScope (F <$> CApp tracetf c))) $
                    EVariant "IfThen" (ERecord [("cond", liftCE (tCondId (F . F))), ("then", EVar (B ()))])))
      (EApp (F <$> trace' tracetf value (TT c) eElse)
            (ETLam KType $ ELam (TT (toScope (CApp (F <$> tracetf) (CVar (B ()))))) $ toScope $
               EApp (ETApp (EVar (F (B ()))) (toScope (F <$> CApp tracetf c))) $
                    EVariant "IfElse" (ERecord [("cond", liftCE (tCondId (F . F))), ("else", EVar (B ()))])))
  where
    tCondId lifting = EApp (lifting <$> trace' tracetf value (TT CBool) eCond) (traceId tracetf)
    
trace' _ _ _t _e = error "missing case in trace' or nonsensical type?"

trace :: Type Constructor String -> Expr Constructor String String -> Expr Constructor String String
trace = trace' (CVar "TRACE") "value"


putE :: Expr Constructor String String -> IO ()
putE e = do
  putDoc $ prettyExpr (evars, tvars) False e
  putStrLn ""

someFunc :: IO ()
someFunc = do
  -- putDoc $ prettyConstructor tvars False (CApp (clam "x" KType (CVar "x")) (clam "y" KType CBool))
  -- putStrLn ""
  -- putDoc $ prettyType tvars False test
  -- putStrLn ""
  -- putDoc $ prettyExpr (evars, tvars) False idA
  -- putStrLn ""
  -- putDoc $ prettyExpr (evars, tvars) False polyId
  -- putStrLn ""
  -- putDoc $ prettyExpr (evars, tvars) False (trace (TT CBool) ETrue)
  -- putStrLn ""
  -- putDoc $ prettyExpr (evars, tvars) False (trace (TT (CList CBool))  (EVar "foo"))
  -- putStrLn ""
  -- putDoc $ prettyExpr (evars, tvars) False (trace (TT (CList CBool)) EEmptyList)
  -- putStrLn ""
  -- putDoc $ prettyExpr (evars, tvars) False (trace (TT (CList CBool)) (ESingletonList ETrue))
  -- putStrLn ""
  -- putE (ETApp polyId (CVar "foo"))
  -- putE $ betaReduceN 1 $ ETApp polyId (CVar "foo")
  -- putE $ betaReduceN 1 (ETApp traceId (CVar "foo"))
  -- putE $ betaReduceN 0 (EApp (trace (TT (CList (CList CBool))) (ESingletonList (ESingletonList ETrue))) traceId)
  let simpleFor = efor "m" (TT (CVar "am")) (EVar "M") (EVar "N") --(ESingeltonList (EVar "m"))
  putE simpleFor
  putE $ betaReduceN 0 $ EApp (trace (TT (CList (CVar "an"))) simpleFor) (traceId (CVar "TRACE"))
  putE $ betaReduceN 1 $ EApp (trace (TT (CList (CVar "an"))) simpleFor) (traceId (CVar "TRACE"))
  putE $ betaReduceN 2 $ EApp (trace (TT (CList (CVar "an"))) simpleFor) (traceId (CVar "TRACE"))
  putE $ betaReduceN 3 $ EApp (trace (TT (CList (CVar "an"))) simpleFor) (traceId (CVar "TRACE"))
  putE $ betaReduceN 4 $ EApp (trace (TT (CList (CVar "an"))) simpleFor) (traceId (CVar "TRACE"))
  -- let forNested = efor "a" (EVar "as") (efor "b" (EVar "bs") (ESingletonList (ERecord [("a", EVar "a"), ("b", EVar "b")])))
  -- putE forNested
  -- putE $ betaReduceN 9 $ trace forNested

  -- let ifThenElse = EIf (EVar "COND") (EVar "THEN") (EVar "ELSE")
  -- putE ifThenElse
  -- putE $ betaReduceN 0 $ EApp (trace (TT (CVar "whatev")) ifThenElse) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 8 $ EApp (trace (TT (CVar "whatev")) ifThenElse) (traceId (CVar "TRACE"))

  let forIf = efor "x" (TT CBool) (EConcat (EVar "xs") (EVar "ys")) (EIf ETrue (ESingletonList (EVar "x")) EEmptyList)
  putE forIf
  putE $ betaReduceN 0 $ EApp (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 1 $ EApp (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 2 $ EApp (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 3 $ EApp (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 4 $ EApp (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 5 $ EApp (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 6 $ EApp (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 7 $ EApp (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  -- putE $ betaReduceN 8 $ EApp (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
  putE $ betaReduceN 9 $ EApp (trace (TT (CList CBool)) forIf) (traceId (CVar "TRACE"))
