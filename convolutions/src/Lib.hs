{-# LANGUAGE BangPatterns #-}

module Lib
    ( convolution, convoluted, convolutedBang, convolutionLazier
    ) where

-- specialized to Int, so I don't get complaints about not being able to chose an instance or whatnot. I should probably annotate the lists instead.
-- [a] -> [b] -> [(a, b)]
convolution :: [Int] -> [Int] -> [(Int, Int)]
convolution as bs = zip as (reverse bs)

-- zip [1..10] (reverse [1..10]) = case [1..10] (reverse [1..10]) of
--   [] _ -> []
--   _ [] -> []
--   (a:as) (b:bs) -> (a, b):zip as bs
--   = case 1:[2..10] (rev (1:[2..10]) []) of
--     [] _ -> []
--     _ [] -> []
--     (a:as) (b:bs) -> (a, b):zip as bs
--   = case 1:[2..10] (rev [2..10] (1:[])) of
-- Even if we only demand whnf, the definition of zip demands to know
-- whether (reverse bs) is empty or not, and the definition of reverse
-- means we have to go all the way to the end to find that out.

convolutionLazier :: [Int] -> [Int] -> [(Int, Int)]
convolutionLazier as bs = zip' as (reverse bs)
  where zip' [] _ = []
        zip' (a:as) bs = (a, head bs):zip' as (tail bs)


convoluted :: [Int] -> [Int] -> [(Int, Int)]
convoluted as bs = snd (go as)
  where
    go [] = (bs, [])
    go (a':as') = let (b':bs', acc) = go as'
                  in (bs', (a', b'):acc)

-- Convoluted get's to cheat if we demand only whnf: If we don't look
-- at b' we never have to traverse bs at all and only need to look at
-- the first element of as.

-- convoluted [1..] [1..] = snd (go as)
-- = let (_, r) = go [1..] in r
-- = let (_, r) = let (b':bs', acc) = go [2..] in (_, (1, b'):acc) in r
-- = (1, b'):acc

convolutedBang :: [Int] -> [Int] -> [(Int, Int)]
convolutedBang as bs = snd (go as)
  where
    go [] = (bs, [])
    go (a':as') = let !(!(b':bs'), acc) = go as'
                  in (bs', (a',b'):acc)
