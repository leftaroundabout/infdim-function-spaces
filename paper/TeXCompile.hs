import System.Process
import System.Directory
    
workDir :: FilePath
workDir = "paper"

thisDocument :: FilePath
thisDocument = "infdimFuncSpaceType-lazyEval-waveletRepr"

main :: IO ()
main = do
  setCurrentDirectory workDir
  mapM_ (`callProcess`[thisDocument]) ["xelatex"]
   
