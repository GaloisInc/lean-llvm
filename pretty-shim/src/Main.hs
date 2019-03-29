{-# LANGUAGE LambdaCase #-}
module Main where

import System.Environment
import System.Exit

import LeanPP
import Data.LLVM.BitCode

main :: IO ()
main = getArgs >>= \case
  [fp] -> shim fp
  _ -> fail "Expected a single filename argument"

shim :: FilePath -> IO ()
shim fp =
  parseBitCodeFromFile fp >>= \case
    Left err -> fail (show err)
    Right m  -> print (llvm_module m)
