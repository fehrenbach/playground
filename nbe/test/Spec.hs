import Test.Hspec
import Lib

-- `main` is here so that this module can be run from GHCi on its own.  It is
-- not needed for automatic spec discovery.
main :: IO ()
main = hspec spec

k = Lam 0 (Lam 1 (Var 0))
s = Lam 0 (Lam 1 (Lam 2 (App (App (Var 0) (Var 2)) (App (Var 1) (Var 2)))))
skk = App (App s k) k

idt = Arrow (Basic "a") (Basic "a")
idt' = Arrow (Arrow (Basic "a") (Basic "b")) (Arrow (Basic "a") (Basic "b"))

ab = Record [ ("a", Str "foo")
            , ("b", Str "bar") ]

spec :: Spec
spec = do
  describe "Wikipedia examples" $ do
    it "normalises SKK at simple id type" $ do
      nbe idt skk `shouldBe` Lam 0 (Var 0)
    it "normalises SKK at complex id type" $ do
      nbe idt' skk `shouldBe` Lam 0 (Lam 1 (App (Var 0) (Var 1)))
  describe "Records" $ do
    it "normalise dynproj a ab at string type" $ do
      nbe StringT (DynProj (Str "a") ab) `shouldBe` Str "foo"
    it "ab!(skk \"a\") ~> \"foo\" at String type" $ do
      nbe StringT (DynProj (App skk (Str "a")) ab) `shouldBe` Str "foo"
    it "{a = skk, b = \"blubb\"}!(skk \"a\") ~> skk at id type" $ do
      nbe idt (DynProj (App skk (Str "a")) (Record [ ("a", skk), ("b", Str "blubb") ])) `shouldBe` Lam 0 (Var 0)
    it "\\foo.{a = foo, b = 'bar'}.'a' ~> \\foo.foo" $ do
      nbe (Arrow (Basic "foo") (Basic "foo")) (Lam 0 (DynProj (Str "a") (Record [ ("a", Var 0), ("b", Str "bar") ]))) `shouldBe` Lam 0 (Var 0)
    it "\\r.r!'a' ~> \\r.r!'a' with precise record type" $ do
      nbe (Arrow (RecordT [("a", Basic "r")]) (Basic "r")) (Lam 0 (DynProj (Str "a") (Var 0))) `shouldBe` (Lam 0 (DynProj (Str "a") (Var 0)))
    it "\\r.r!'a' ~> \\r.r!'a' with added label in record type" $ do
      nbe (Arrow (RecordT [("a", Basic "r"), ("b", StringT)]) (Basic "r")) (Lam 0 (DynProj (Str "a") (Var 0))) `shouldBe` (Lam 0 (DynProj (Str "a") (Var 0)))
    it "\\r.r!(skk 'a') ~> \\r.r!'a' with added label in record type" $ do
      nbe (Arrow (RecordT [("a", Basic "r"), ("b", StringT)]) (Basic "r"))
          (Lam 0 (DynProj (App skk (Str "a")) (Var 0))) `shouldBe` (Lam 0 (DynProj (Str "a") (Var 0)))
  -- describe "Variants" $ do
  --   it "Variant identity at precise type" $ do
  --     nbe (VariantT [("a", StringT)]) (Variant "a" (Str "foo")) `shouldBe` (Variant "a" (Str "foo"))
  --   it "Variant identity at more general type" $ do
  --     nbe (VariantT [("a", StringT), ("b", Basic "foo")]) (Variant "a" (Str "foo")) `shouldBe` (Variant "a" (Str "foo"))
  --   it "Simple SWITCH" $ do
  --     nbe StringT (Switch (Variant "a" (Str "foo")) [("a", 0, Var 0)] ) `shouldBe` Str "foo"
  --   it "Useless cases in SWITCH" $ do
  --     nbe StringT (Switch (Variant "a" (Str "foo")) [("a", 0, Var 0), ("b", 1, Var 1)] ) `shouldBe` Str "foo"
  --   it "Normalize in case body" $ do
  --     nbe StringT (Switch (Variant "a" ab) [("a", 0, DynProj (Str "a") (Var 0)), ("b", 1, Var 1)] ) `shouldBe` Str "foo"
  --   it "Residual switch" $ do
  --     nbe (Arrow (VariantT [("a", Basic "v")]) (Basic "v"))
  --       (Lam 0 (Switch (Var 0) [("a", 1, Var 1)]))
  --       `shouldBe`
  --       (Lam 0 (Switch (Var 0) [("a", 1, Var 1)]))
  --       -- `shouldBe` (Lam 0 (Var 0))
  --   -- it "Precisely typed switch can be normalised away" $ do
  --     -- nbe (Arrow (VariantT [("a", StringT)]) StringT) (Lam 1 (Switch (Var 1) [("a", 2, Var 2)]))
  --       -- `shouldBe` (Lam 0 (Var 0))
  --   it "Residual switch 2" $ do
  --     nbe (Arrow (VariantT [("a", StringT)]) StringT)
  --       (Lam 0 (Switch (Var 0) [("a", 1, Var 1)]))
  --       `shouldBe`
  --       (Lam 0 (Switch (Var 0) [("a", 1, Var 1)]))
