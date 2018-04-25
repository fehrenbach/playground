module Main where

import Criterion.Main

-- specialized to Int, so I don't get complaints about not being able to chose an instance or whatnot. I should probably annotate the lists instead.
-- [a] -> [b] -> [(a, b)]
convolution :: [Int] -> [Int] -> [(Int, Int)]
convolution as bs = zip as (reverse bs)

convoluted :: [Int] -> [Int] -> [(Int, Int)]
convoluted as bs = snd (go as)
  where
    go [] = (bs, [])
    go (a':as') = let (b':bs', acc) = go as'
                  in (bs', (a', b'):acc)

main :: IO ()
main = defaultMain [
  bgroup "convolution" [--  bench "1" $ nf (uncurry convolution) ([1], [1])
                       -- ,
                        --  bench "10" $ nf (uncurry convolution) ([1..10], [1..10])
                       -- ,
                         bench "100" $ nf (uncurry convolution) ([1..100], [1..100])
                       , bench "1000" $ nf (uncurry convolution) ([1..1000], [1..1000])
                       , bench "10000" $ nf (uncurry convolution) ([1..10000], [1..10000])
                       , bench "100000" $ nf (uncurry convolution) ([1..100000], [1..100000])
                       , bench "1000000" $ nf (uncurry convolution) ([1..1000000], [1..1000000])
                       -- , bench "10000000" $ nf (uncurry convolution) ([1..10000000], [1..10000000])
                       ],
  bgroup "convoluted" [ -- bench "1" $ nf (uncurry convoluted) ([1], [1])
                      -- , 
                        -- bench "10" $ nf (uncurry convoluted) ([1..10], [1..10])
                      -- , 
                        bench "100" $ nf (uncurry convoluted) ([1..100], [1..100])
                      , bench "1000" $ nf (uncurry convoluted) ([1..1000], [1..1000])
                      , bench "10000" $ nf (uncurry convoluted) ([1..10000], [1..10000])
                      , bench "100000" $ nf (uncurry convoluted) ([1..100000], [1..100000])
                      , bench "1000000" $ nf (uncurry convoluted) ([1..1000000], [1..1000000])
                      -- , bench "10000000" $ nf (uncurry convoluted) ([1..10000000], [1..10000000])
                      ]
  ]
