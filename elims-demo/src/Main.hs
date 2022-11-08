{-# language UnicodeSyntax #-}

module Main where

import System.Environment
import Impl

main ∷ IO ()
main = do
  args ← getArgs
  case args of
    path:_ → runHIITDefs path
    _ → putStrLn "hiit-defs: no input file"
