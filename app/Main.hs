module Main where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Language.Horn.Codegen (compile)
import Language.Horn.Parse (parseProg)
import System.Environment (getArgs)
import Text.Megaparsec (errorBundlePretty, parse)

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
  let program = either (error . errorBundlePretty) id $ parseProg original src
      code = compile program
  if output == "-"
    then TIO.putStrLn code
    else TIO.writeFile output code
