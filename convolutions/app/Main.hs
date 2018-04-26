module Main where

import Lib (convolution, convoluted, convolutedBang, convolutionLazier)
import Criterion.Main

b size norm fun = bench (show size) $ norm (uncurry fun) ([1..size], [1..size])

sizes = [100, 1000, 10000]

main :: IO ()
main = defaultMain
  [ bgroup "nf/convolution"       [b size nf convolution | size <- sizes ]
  , bgroup "nf/convoluted"        [b size nf convoluted | size <- sizes ]
  , bgroup "nf/convolutedBang"    [b size nf convolutedBang | size <- sizes ]
  , bgroup "nf/convolutionLazier" [b size nf convolutionLazier | size <- sizes ]
  , bgroup "whnf/convolution"       [b size whnf convolution | size <- sizes ]
  , bgroup "whnf/convoluted"        [b size whnf convoluted | size <- sizes ]
  , bgroup "whnf/convolutedBang"    [b size whnf convolutedBang | size <- sizes ]
  , bgroup "whnf/convolutionLazier" [b size whnf convolutionLazier | size <- sizes ]
  , bgroup "nfhead/convolution"       [b size (\f -> nf (head . f)) convolution | size <- sizes ]
  , bgroup "nfhead/convoluted"        [b size (\f -> nf (head . f)) convoluted | size <- sizes ]
  , bgroup "nfhead/convolutedBang"    [b size (\f -> nf (head . f)) convolutedBang | size <- sizes ]
  , bgroup "nfhead/convolutionLazier" [b size (\f -> nf (head . f)) convolutionLazier | size <- sizes ]
  ]
