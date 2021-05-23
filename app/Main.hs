module Main where

import Codegen (compile)
import Parse (parseProg)

import qualified Data.Text.IO as TIO
import System.Directory (doesFileExist, getModificationTime)
import System.Environment (getArgs)
import Text.Megaparsec (errorBundlePretty)

main :: IO ()
main = do
  args <- getArgs
  case args of
    original:input:output:_ -> runConvert original input output
    input:output:_ -> runConvert input input output
    input:_ -> runConvert input input "-"
    [] -> fail "missing input file"

runConvert :: FilePath -> FilePath -> FilePath -> IO ()
runConvert original input output = do
  src <- TIO.readFile input
  program <- either (fail . errorBundlePretty) pure $ parseProg original src
  if output == "-"
    then TIO.putStrLn $ compile program
    else do
      let pp = original ++ "pp"
      ppExists <- doesFileExist pp
      res <-
        if ppExists
          then do
            ppMtime <- getModificationTime pp
            originalMtime <- getModificationTime original
            if originalMtime <= ppMtime
              then TIO.readFile pp
              else pure $ compile program
          else pure $ compile program
      TIO.writeFile pp res
      TIO.writeFile output res
