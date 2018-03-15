module Common where

import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

type Label = String

pparens :: Bool -> Doc -> Doc
pparens True d = black (char '(') <> d <> black (char ')')
pparens False d = d

