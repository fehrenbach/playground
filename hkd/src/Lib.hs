{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeFamilies #-}

module Lib
    ( someFunc
    ) where

import Data.Functor.Identity
import Control.Monad

-- http://reasonablypolymorphic.com/blog/higher-kinded-data/

data Person' f = Person'
  { name :: HKD f String
  , age :: HKD f Int }

type Person = Person' Identity
type PartialPerson = Person' Maybe

type family HKD f a where
  HKD Identity a = a
  HKD f a = f a

complete :: PartialPerson -> Maybe Person
complete (Person' { name, age }) =
  Person' <$> name <*> age

someFunc :: IO ()
someFunc = putStrLn "someFunc"
