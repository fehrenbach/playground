module Lib
    ( someFunc
    ) where

import Expr

someFunc :: IO ()
someFunc = do
  -- putStrLn (show boatTours)
  putStrLn (show (symev [] boatTours))
  putStrLn (show (symev [] untracedAgencies))
