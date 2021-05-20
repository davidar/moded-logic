module Main where

import qualified Data.Text.IO as TIO
import Language.Horn.Codegen (compile)
import Language.Horn.Parse (parseProg)
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
    else TIO.writeFile output $ compile program
