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
  let embedD¹ (l,r) f x
       | x>l && x<r  = f . D¹ $ 2*(x-l)/(r-l) - 1
       | otherwise   = 0/0
  mkPlotFigure "simple-PCM-example.pdf" (Dia.dims $ 560 ^& 480)
     ( let f (D¹ x) = sin (3*x) - cos (7*x)/3 - 0.2
           res = 12
           h = 2/fromIntegral res
           fPCM = [(x, f $ D¹ x) | x <- [h/2-1, 3*h/2-1 .. 1-h/2]]
       in [ continFnPlot (embedD¹ (-1,1) f) & legendName "𝑓"
          , shapePlot (mconcat
             [ Dia.circle (h/9) & Dia.moveTo (x^&y)
             | (x,y) <- fPCM ]) & legendName ("PCM (𝑛="++show res++")")
          , xAxisLabel "𝑥"
          , yAxisLabel "𝑓(𝑥)" ] )
     HorizontalCatLegend
  mkPlotFigure "Haar-domDecompose.pdf" (Dia.dims $ 560 ^& 480)
     ( let f (D¹ x) = sin (3*x) - cos (7*x)/3 - 0.2
           fHaar = homsampleHaarFunction (TwoToThe 10) f
           (y₀, (fl, fr)) = multiscaleDecompose fHaar
           δlr = (fst (multiscaleDecompose fr) - fst (multiscaleDecompose fl))/2
           f₀ _ = y₀
       in [ continFnPlot (embedD¹ (-1,1) f) & legendName "𝑓"
          , continFnPlot (embedD¹ (-1,1) f₀) & legendName "offset"
          , continFnPlot (embedD¹ (-1,1) $ \(D¹ x)
                            -> if x<0 then -δlr else δlr) & legendName "δlr"
          , continFnPlot (embedD¹ (-1,0) $ (+δlr)
                                   . evalHaarFunction fl) & legendName "𝑓l"
          , continFnPlot (embedD¹ ( 0,1) $ subtract δlr
                                   . evalHaarFunction fr) & legendName "𝑓r"
          , xAxisLabel "𝑥"
          , yAxisLabel "𝑓(𝑥)" ] )
     HorizontalCatLegend
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
