import System.Process
import System.Directory

import Math.Function.FiniteElement.PWConst
import Data.Manifold.Types
import Data.VectorSpace

import Graphics.Dynamic.Plot.R2

import qualified Diagrams.Prelude as Dia
import Diagrams.Backend.Cairo
import Diagrams.Backend.Cairo.Internal (Options(CairoOptions))
import Diagrams.Prelude (V2(..), (^&), renderDia)
import Data.Default.Class
import Data.Function ((&))
import Control.Lens ((.~), (^.))
    
workDir :: FilePath
workDir = "paper"

thisDocument :: FilePath
thisDocument = "infdimFuncSpaceType-lazyEval-waveletRepr"

main :: IO ()
main = do
  setCurrentDirectory workDir
  mapM_ (`callProcess`[thisDocument]) ["xelatex"]
   
data LegendConfig = VerticalStackLegend | HorizontalCatLegend

mkPlotFigure :: String -> Dia.SizeSpec V2 ℝ -> [DynamicPlottable] -> LegendConfig -> IO ()
mkPlotFigure fname size plots legendCfg = do
      dia <- plotPrerender (def & xResV .~ round width
                                & yResV .~ round height
                                & prerenderScaling .~ OutputCoordsScaling) plots
      let legendSize = Dia.mkSizeSpec2D (Dia.getSpec size ^. Dia._x) $ case legendCfg of
            HorizontalCatLegend -> Just 1
            VerticalStackLegend -> Nothing
      legend <- plotLegendPrerender (def & legendPrerenderSize .~ legendSize) plots 
      fst . renderDia Cairo (CairoOptions fname size PDF False)
          $ Dia.composeAligned Dia.alignL (Dia.cat $ negateV Dia.unit_Y) $ reverse
             [ dia
             , maybe mempty id legend ]
      return ()
 where width = case Dia.getSpec size ^. Dia._x of
          Nothing -> 640
          Just w -> w
       height = case Dia.getSpec size ^. Dia._y of
          Nothing -> 480
          Just h -> h
