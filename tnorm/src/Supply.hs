{-# LANGUAGE MultiParamTypeClasses #-}
module Supply where

class Monad m => MonadSupply v m where
  fresh :: m v
