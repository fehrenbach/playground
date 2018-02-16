{-# LANGUAGE InstanceSigs, FlexibleContexts, DeriveFunctor, StandaloneDeriving, TemplateHaskell, RankNTypes, ScopedTypeVariables #-}

module Lib
    ( someFunc
    ) where

import Bound ((>>>=), Var(B,F))
import Bound.Scope.Simple
import Control.Monad (ap)
import Control.Monad.Morph (lift)
import Data.Functor.Classes (Eq1)
import Data.Deriving (deriveEq1)
import Text.PrettyPrint.ANSI.Leijen

pparens :: Bool -> Doc -> Doc
pparens True = parens
pparens False = id

data Kind = KType | KArrow Kind Kind
  deriving (Eq)

prettyKind :: Kind -> Doc
prettyKind KType = text "Type"
prettyKind (KArrow l r) = parens $ prettyKind l <+> text "->" <+> prettyKind r 

type Label = String

data Constructor a
  = CBool
  | CVar a
  | CLambda Kind (Scope () Constructor a)
  | CApp (Constructor a) (Constructor a)
  | CList (Constructor a)
  -- I don't really want another datatype
  | CRowNil
  | CRowCons Label (Constructor a) (Constructor a)
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
  CRowNil >>= _ = CRowNil
  CRowCons l c r >>= f = CRowCons l (c >>= f) (r >>= f)

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

data Type c a
  = TBool
  | TT (c a)
  -- the body is a type with an additional bound constructor variable
  | TForall Kind (Type (Scope () c) a)
  | TArrow (Type c a) (Type c a)
  | TList (Type c a)
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
    go f a TBool = TBool
    go f a (TT c) = TT (f a c)
    go f a (TForall k b) = TForall k (go f' a b)
      where
        f' v = Scope . f (F v) . unscope
    go f a (TArrow l r) = TArrow (go f a l) (go f a r)
    go f a (TList t) = TList (go f a t)

test :: Type Constructor String
test = tforall "foo" KType (TT (CApp (clam "ex" KType (CVar "ex")) (CVar "foo")))

prettyType :: [String] -> Bool -> Type Constructor String -> Doc
prettyType [] _ _ = error "ran out of type variables during type pretty printing"
prettyType _ _ TBool = text "Bool"
prettyType avs _ (TT c) = char 'T' <> parens (prettyConstructor avs False c)
prettyType (av:avs) p (TForall k body) = pparens p $
  char '∀' <> text av <> char ':' <> prettyKind k <> char '.' <> prettyType avs p (tInstantiate1 (CVar av) body)
prettyType avs p (TArrow a b) = pparens p $ prettyType avs True a <+> text "->" <+> prettyType avs True b
prettyType avs p (TList a) = pparens p $ text "List" <+> prettyType avs True a

tInstantiate1 :: forall operand b a.
  (Applicative operand, Monad operand) =>
  operand a -> Type (Scope b operand) a -> Type operand a
tInstantiate1 = go instantiate1
  where
    go :: forall o o' u. (forall v. operand v -> o v -> o' v) -> operand u -> Type o u -> Type o' u
    go f a TBool = TBool
    go f a (TT c) = TT (f a c)
    go f a (TForall k b) = TForall k (go f' a b)
      where
        f' v = Scope . f (fmap F v) . unscope
    go f a (TArrow l r) = TArrow (go f a l) (go f a r)
    go f a (TList t) = TList (go f a t)

data Expr c a x
  = ETrue
  | EVar x
  | ELam (Type c a) (Scope () (Expr c a) x)
  | EApp (Expr c a x) (Expr c a x)
  | ETLam Kind (Expr (Scope () c) a x)
  | EVariant Label (Expr c a x) -- add type hint?
  | EEmptyList -- add type hint? (Type c a)
  | ESingletonList (Expr c a x)
  | EConcat (Expr c a x) (Expr c a x)
  | EFor {- (Type c a) -} (Expr c a x) (Scope () (Expr c a) x)
  | EEmptyRecord
  | ERecordExt Label (Expr c a x) (Expr c a x)
  deriving (Functor)

instance (Eq a, Monad c) => Applicative (Expr c a) where
  pure = return
  (<*>) = ap

instance (Eq a, Monad c) => Monad (Expr c a) where
  return = EVar

  ETrue >>= _ = ETrue
  EVar x >>= f = f x
  ELam t b >>= f = ELam t (b >>>= f)
  EFor e b >>= f = EFor (e >>= f) (b >>>= f)
  EApp l r >>= f = EApp (l >>= f) (r >>= f)
  ETLam k b >>= f = ETLam k (b >>= liftCE . f)
  EVariant l e >>= f = EVariant l (e >>= f)
  EEmptyList >>= _ = EEmptyList
  ESingletonList e >>= f = ESingletonList (e >>= f)
  EConcat l r >>= f = EConcat (l >>= f) (r >>= f)
  EEmptyRecord >>= _ = EEmptyRecord
  ERecordExt l x r >>= f = ERecordExt l (x >>= f) (r >>= f)

liftCE :: Monad c => Expr c a b -> Expr (Scope () c) a b
liftCE ETrue = ETrue
liftCE (EVar x) = EVar x
liftCE (ELam t b) = ELam (liftCT t) (hoistScope liftCE b)
liftCE (EFor e b) = EFor (liftCE e) (hoistScope liftCE b)
liftCE (EApp l r) = EApp (liftCE l) (liftCE r)
liftCE (ETLam k b) = ETLam k (liftCE b)
liftCE (EVariant l e) = EVariant l (liftCE e)
liftCE EEmptyList = EEmptyList
liftCE (ESingletonList e) = ESingletonList (liftCE e)
liftCE (EConcat l r) = EConcat (liftCE l) (liftCE r)

liftCT :: Monad c => Type c a -> Type (Scope () c) a
liftCT TBool = TBool
liftCT (TT c) = TT (lift c)
liftCT (TForall k c) = TForall k (liftCT c)
liftCT (TArrow a b) = TArrow (liftCT a) (liftCT b)
liftCT (TList a) = TList (liftCT a)

elam :: Eq x => x -> Type c a -> Expr c a x -> Expr c a x
elam x t b = ELam t (abstract1 x b)

efor :: Eq x => x -> Expr c a x -> Expr c a x -> Expr c a x
efor x i o = EFor i (abstract1 x o)

record :: [(Label, Expr c a x)] -> Expr c a x
record [] = EEmptyRecord
record ((l, x) : r) = ERecordExt l x (record r)

idA :: Expr Constructor String String
idA = elam "ex" (TT (CVar "a")) (EVar "ex")

-- instantiate a constructor in an expression
eInstantiateC1 :: Eq a => Monad c => c a -> Expr (Scope () c) a x -> Expr c a x
eInstantiateC1 a ETrue = ETrue
eInstantiateC1 a (EVar x) = EVar x
eInstantiateC1 a (ELam t b) = ELam (tInstantiate1 a t) (hoistScope (eInstantiateC1 a) b)
eInstantiateC1 a (EApp l r) = EApp (eInstantiateC1 a l) (eInstantiateC1 a r)
eInstantiateC1 a (ETLam k b) = ETLam k (eInstantiateC1 (lift a) b)
eInstantiateC1 a EEmptyList = EEmptyList
eInstantiateC1 a (EVariant l e) = EVariant l (eInstantiateC1 a e)
eInstantiateC1 a (ESingletonList e) = ESingletonList (eInstantiateC1 a e)
eInstantiateC1 a (EConcat l r) = EConcat (eInstantiateC1 a l) (eInstantiateC1 a r)
eInstantiateC1 a (EFor i o) = EFor (eInstantiateC1 a i) (hoistScope (eInstantiateC1 a) o)


-- abstract over a constructor in an expression
eAbstractC1 :: Eq a => Functor c => a -> Expr c a x -> Expr (Scope () c) a x
eAbstractC1 a ETrue = ETrue
eAbstractC1 a (EVar x) = EVar x
eAbstractC1 a (ELam t b) = ELam (tAbstract1 a t) (hoistScope (eAbstractC1 a) b)
eAbstractC1 a (EApp l r) = EApp (eAbstractC1 a l) (eAbstractC1 a r)
eAbstractC1 a (ETLam k b) = ETLam k (eAbstractC1 a b)
eAbstractC1 a EEmptyList = EEmptyList
eAbstractC1 a (EVariant l e) = EVariant l (eAbstractC1 a e)
eAbstractC1 a (ESingletonList e) = ESingletonList (eAbstractC1 a e)
eAbstractC1 a (EConcat l r) = EConcat (eAbstractC1 a l) (eAbstractC1 a r)
eAbstractC1 a (EFor i o) = EFor (eAbstractC1 a i) (hoistScope (eAbstractC1 a) o)

etlam :: Eq a => Monad c => a -> Kind -> Expr c a x -> Expr c a x
etlam a k b = ETLam k (eAbstractC1 a b) -- this should be actual abstract, not my misnamed one, I think

polyId :: Expr Constructor String String
polyId = etlam "a" KType (elam "ex" (TT (CVar "a")) (EVar "ex"))

prettyExpr :: ([String], [String]) -> Bool -> Expr Constructor String String -> Doc
prettyExpr ([], _) _ _ = error "ran out of variable names"
prettyExpr (_, []) _ _ = error "ran out of type variable names"
prettyExpr _ _ ETrue = text "true"
prettyExpr _ _ (EVar x) = text x
prettyExpr (v:vs, tvs) p (ELam t b) = pparens p $ hang 2 $
  char 'λ' <> text v <> char ':' <> prettyType tvs False t <> char '.' <//> prettyExpr (vs, tvs) False (instantiate1 (EVar v) b)
prettyExpr (vs, tv:tvs) p (ETLam k b) = pparens p $
  char 'Λ' <> text tv <> char ':' <> prettyKind k <> char '.' <//> prettyExpr (vs, tvs) False (eInstantiateC1 (CVar tv) b)
prettyExpr ns p (EVariant l e) = pparens p $
  dullgreen (text l) <+> prettyExpr ns True e
prettyExpr ns p (EApp l r) = pparens p $
  prettyExpr ns True l </> prettyExpr ns True r
prettyExpr ns p EEmptyList = text "[]"
prettyExpr ns p (ESingletonList e) = brackets $ prettyExpr ns False e
prettyExpr ns p (EConcat l r) = pparens p $ prettyExpr ns True l <+> text "++" <+> prettyExpr ns True r
prettyExpr (v:vs, tvs) p (EFor i o) = pparens p $ hang 2 $
  bold (text "for") <+> parens (text v <+> text "<-" <+> prettyExpr (v:vs, tvs) False i) </> prettyExpr (vs, tvs) False (instantiate1 (EVar v) o)
prettyExpr ns p EEmptyRecord = braces empty
prettyExpr ns p r@(ERecordExt _ _ _) = braces $ align $ printRecord ns r

printRecord ns EEmptyRecord = empty
printRecord ns (ERecordExt l x EEmptyRecord) = blue (text l) <+> char '=' <+> prettyExpr ns False x
printRecord ns (ERecordExt l x r) = blue (text l) <+> char '=' <+> prettyExpr ns False x <> char ',' </> printRecord ns r

{-

-- deriveShow1 ''Type
-- instance Show a => Show (Type a) where showsPrec = showsPrec1


-- bitraverse?
-- freeVariables :: Expr (Type String) String -> [String]
-- freeVariables = bitraverse
-}

tvars = ["α", "β", "γ"] <> [ "α" <> show x | x <- [0..] ]
evars = ["x", "y", "z"] <> [ "x" <> show x | x <- [0..] ]

ttype :: Constructor String -> Type Constructor String
ttype c = TArrow (TT (CApp (CVar "TRACE") c)) (TT (CApp (CVar "TRACE") c))

trace :: Expr Constructor String String -> Expr Constructor String String
trace ETrue = elam "t" (ttype CBool) (EApp (EVar "t") (EVariant "Lit" ETrue))
trace (EVar x) = elam "t" (ttype (CVar "??")) (EApp (EVar "t") (EVar x))
trace (ELam _ _) = error "cannot trace lambda"
trace (ETLam _ _) = error "cannot trace Lambda"
trace (EApp _ _) = error "cannot trace app"
trace (EVariant _ _) = error "cannot trace variant constructor"
trace EEmptyList = elam "t" (ttype (CVar "??")) EEmptyList
trace (ESingletonList e) = elam "t" (ttype (CVar "??")) (ESingletonList (EApp (trace e) (EVar "t")))
trace (EConcat l r) = elam "t" (ttype (CVar "??")) (EConcat (efor "l" (EApp (trace l) (EVar "t")) (ESingletonList (EVar "l"))) (efor "r" (EApp (trace r) (EVar "t")) (ESingletonList (EVar "r"))))
trace (EFor i o) = -- not sure this makes any sense
 elam "t" (ttype (CVar "??")) $
  efor "i" (EApp (trace i) (elam "x" (TT (CVar "???")) (EVar "x"))) $ {- TODO replace by proper identity function -}
    (EApp (trace (instantiate (const (EVar "i")) o))
      (elam "o" (TT (CVar "????")) (EApp (EVar "t") (EVariant "For" (record [("in", EVar "i"), ("out", EVar "o")])))))

betaReduce :: Eq x => Monad c => Expr c x a -> Expr c x a
betaReduce ETrue = ETrue
betaReduce (EApp (ELam _ b) x) = instantiate1 x b
betaReduce (EApp f x) = EApp (betaReduce f) (betaReduce x)
betaReduce (EVar x) = EVar x
betaReduce (ELam t b) = ELam t (hoistScope betaReduce b)
betaReduce (ETLam k b) = ETLam k (betaReduce b)
betaReduce (EVariant l e) = EVariant l (betaReduce e)
betaReduce (ESingletonList e) = ESingletonList (betaReduce e)
betaReduce EEmptyList = EEmptyList
betaReduce (EConcat l r) = EConcat (betaReduce l) (betaReduce r)
betaReduce (EFor i o) = EFor (betaReduce i) (hoistScope betaReduce o)

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
  -- putDoc $ prettyExpr (evars, tvars) False (trace ETrue)
  -- putStrLn ""
  -- putDoc $ prettyExpr (evars, tvars) False (trace (EVar "foo"))
  -- putStrLn ""
  -- putDoc $ prettyExpr (evars, tvars) False (trace EEmptyList)
  -- putStrLn ""
  -- putDoc $ prettyExpr (evars, tvars) False (trace (ESingletonList ETrue))
  -- putStrLn ""
  -- putDoc $ prettyExpr (evars, tvars) False (trace (ESingletonList (ESingletonList ETrue)))
  -- putStrLn ""
  -- putDoc $ prettyExpr (evars, tvars) False (trace (EConcat (ESingletonList ETrue) EEmptyList))
  -- putStrLn ""
  -- putDoc $ prettyExpr (evars, tvars) False $ efor "x" (EVar "inList") (ESingletonList (EVar "x"))
  -- putStrLn ""
  -- putDoc $ prettyExpr (evars, tvars) False (trace (efor "x" (EVar "inList") (ESingletonList (EVar "x"))))
  -- putStrLn ""
  -- putDoc $ prettyExpr (evars, tvars) False ((betaReduce . betaReduce . betaReduce) (trace (efor "x" (EVar "inList") (ESingletonList (EVar "x")))))
  -- putStrLn ""
  putDoc $ prettyExpr (evars, tvars) False (efor "x" (EVar "as") (efor "y" (EVar "bs") (EConcat (ESingletonList (EVar "x")) (ESingletonList (EVar "y")))))
  putStrLn ""
  putDoc $ prettyExpr (evars, tvars) False (trace (efor "x" (EVar "as") (efor "y" (EVar "bs") (EConcat (ESingletonList (EVar "x")) (ESingletonList (EVar "y"))))))
  putStrLn ""
  putDoc $ prettyExpr (evars, tvars) False ((betaReduce . betaReduce . betaReduce . betaReduce . betaReduce . betaReduce . betaReduce . betaReduce)  (EApp (trace (efor "x" (EVar "xs") (efor "y" (EVar "ys") (EConcat (ESingletonList (EVar "x")) (ESingletonList (EVar "y")))))) idA))
  putStrLn ""
