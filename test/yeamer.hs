-- This work is licensed under the Creative Commons Attribution-NoDerivatives
-- 4.0 International License.
-- To view a copy of this license, visit http://creativecommons.org/licenses/by-nd/4.0/
-- or send a letter to Creative Commons, PO Box 1866, Mountain View, CA 94042, USA.

{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE ImplicitParams      #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE UnicodeSyntax       #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}

import qualified Prelude as Hask
import Control.Category.Constrained.Prelude

import Presentation.Yeamer
import Presentation.Yeamer.Maths
import qualified Math.LaTeX.Prelude as LaTeX
import Math.LaTeX.StringLiterals
import Text.LaTeX.Base.Math (operatorname)
import qualified Text.Blaze.Html as Blaze
import Text.Hamlet
import Text.Cassius

import Data.Semigroup
import Data.Semigroup.Numbered
import Data.List (transpose, inits, tails, partition, minimumBy)
import Data.Ord (comparing)
import Control.Arrow ((>>>), (&&&), first, second)
import Control.Monad (guard)

import Data.Manifold.Types
import Data.Manifold.PseudoAffine
import Data.Manifold.FibreBundle
import Data.Manifold.Web
import qualified Data.Manifold.Web.Internal as Web
import Data.VectorSpace
import Data.VectorSpace.Free
import Math.LinearMap.Category hiding ((⊗))
import Math.Manifold.Embedding.Simple.Class
import Linear.V2
import Linear.V3
import Math.Rotations.Class (Rotatable, AxisSpace, rotateAbout, zAxis)
import qualified Numeric.QD.QuadDouble as QD

import Graphics.Dynamic.Plot.R2
import qualified Diagrams.Prelude as Dia
import qualified Diagrams.Backend.Cairo as Dia
import Diagrams.Prelude (p2)

import System.Environment
import Control.Lens hiding (set, (<.>))
import Control.Concurrent
import Data.IORef
import Text.Printf (printf)
import GHC.Exts (IsString(fromString))
import Data.Default.Class (def)

import qualified Text.Show.Pragmatic as SP

import Math.Function.FiniteElement.PWConst
import Math.Function.FiniteElement.PWConst.Internal
import Math.Function.FiniteElement.PWLinear

class HasIntervalFunctions v where
  fromIntervalFunction :: PowerOfTwo -> (D¹ -> Scalar v) -> v
  visualiseIvFn :: PowerOfTwo -> v -> DynamicPlottable
instance ∀ s . (RealFrac s, Num' s, AffineSpace s, Diff s ~ s, Needle s ~ s)
    => HasIntervalFunctions (Haar_D¹ 'DistributionSpace s) where
  fromIntervalFunction = case closedScalarWitness @s of
    ClosedScalarWitness -> \resoLimit f
     -> case homsampleHaarFunction resoLimit f :: Haar D¹ s of
          fspld -> coRiesz_origReso $ fspld
  visualiseIvFn resoLimit d = continFnPlot $ (realToFrac::s->ℝ) . evalHaarFunction f . D¹
   where f = case closedScalarWitness @s of
          ClosedScalarWitness
           -> riesz_resolimited resoLimit $ d :: Haar_D¹ 'FunctionSpace s
instance ∀ s . (RealFrac s, Num' s, AffineSpace s, Diff s ~ s, Needle s ~ s)
    => HasIntervalFunctions (Haar_D¹ 'FunctionSpace s) where
  fromIntervalFunction = case closedScalarWitness @s of
     ClosedScalarWitness -> homsampleHaarFunction
  visualiseIvFn _ f = continFnPlot $ realToFrac . evalHaarFunction f . D¹

main :: IO ()
main = do
 newPlotLock <- newIORef Nothing
 let ?plotLock = newPlotLock
 
 yeamer . styling style $ do
   ""──
     "global-title"#%
       "Tests of infinite-dimensional-function-space data structures"
   
   "Sinkhorn convergence"
    ====== do
     let visualiseSinkhornConv :: ∀ dn s v
           . ( HasIntervalFunctions v, OptimalTransportable v v, v ~ Haar_D¹ dn s
             , RealFrac s, Num' s, s ~ Needle s, s ~ Scalar s
             , AffineSpace s, s ~ Diff s )
                  => (ℝ->s) -> SinkhornOTConfig -> (ℝ->ℝ, ℝ->ℝ) -> [DynamicPlottable]
         visualiseSinkhornConv convertS shOTC (r₀, c₀)
             = [ continFnPlot $ realToFrac . r
               , plotLatest
                   [ plotDelay 0.5 . plotMultiple
                       $ [mempty,mempty]
                        ++[ visualiseIvFn resoLimit $ marg ot
                          | marg <- [ lMarginal
                                    , case scalarSpaceWitness @v of
                                        ScalarSpaceWitness
                                         -> lMarginal . getLinearFunction transposeTensor ]
                          ]
                   | ot <- entropyLimOptimalTransport shOTC r' c']
               , continFnPlot $ realToFrac . c ]
          where r', c', r₀', c₀' :: v
                [r₀',c₀'] = asDistrib . fmap convertS<$>[r₀,c₀]
                [ar,ac] = pwconst_D¹_offset<$>[r₀',c₀']
                r = ((/ar).convertS)<$>r₀; r'=r₀'^/ar
                c = ((/ac).convertS)<$>c₀; c'=c₀'^/ac
                asDistrib :: (ℝ->s)->v
                asDistrib f = fromIntervalFunction resoLimit $ \(D¹ x)->f x
                resoLimit = TwoToThe 6
         broadPeaks, mediumPeaks, narrowPeaks :: (ℝ->ℝ, ℝ->ℝ)
         broadPeaks = (\x -> exp (-(x-0.4)^2*7), \x -> exp (-(x+0.4)^2*12))
         mediumPeaks = (\x -> exp (-(x-0.4)^2*37), \x -> exp (-(x+0.4)^2*29))
         narrowPeaks = (\x -> exp (-(x-0.4)^2*1072), \x -> exp (-(x+0.4)^2*660))
     "Double-precision floating-point"======
      do
       "DistributionSpace"
        ======
        plotServ
         ( visualiseSinkhornConv @'DistributionSpace id (SinkhornOTConfig 18)
              broadPeaks )
         "Broad peaks. Converges." ──
        plotServ
         ( visualiseSinkhornConv @'DistributionSpace id (SinkhornOTConfig 18)
              mediumPeaks )
         "Medium peaks. Converges." ──
        plotServ
         ( visualiseSinkhornConv @'DistributionSpace id (SinkhornOTConfig 18)
              narrowPeaks )
         "Narrow peaks. Converges." ──
        plotServ
         ( visualiseSinkhornConv @'DistributionSpace id (SinkhornOTConfig 32)
               broadPeaks )
         "λ too big, doesn't converge."
      │do
       "FunctionSpace"
        ======
        plotServ
         ( visualiseSinkhornConv @'FunctionSpace id (SinkhornOTConfig 18)
               broadPeaks )
         "Broad peaks. Converges." ──
        plotServ
         ( visualiseSinkhornConv @'FunctionSpace id (SinkhornOTConfig 18)
               mediumPeaks )
         "Medium peaks. Diverges." ──
        plotServ
         ( visualiseSinkhornConv @'FunctionSpace id (SinkhornOTConfig 18)
               narrowPeaks )
         "Narrow peaks. Diverges." ──
        plotServ
         ( visualiseSinkhornConv @'FunctionSpace id (SinkhornOTConfig 32)
               broadPeaks )
         "λ big, still converges."
     "Quad-double floating-point"======
      do
       "DistributionSpace"
        ======
        plotServ
         ( visualiseSinkhornConv @'DistributionSpace QD.fromDouble (SinkhornOTConfig 18)
               broadPeaks )
         "Broad peaks. Converges." ──
        plotServ
         ( visualiseSinkhornConv @'DistributionSpace QD.fromDouble (SinkhornOTConfig 18)
               mediumPeaks )
         "Medium peaks. Converges." ──
        plotServ
         ( visualiseSinkhornConv @'DistributionSpace QD.fromDouble (SinkhornOTConfig 18)
               narrowPeaks )
         "Narrow peaks. Converges." ──
        plotServ
         ( visualiseSinkhornConv @'DistributionSpace QD.fromDouble (SinkhornOTConfig 32)
               broadPeaks )
         "λ too big, doesn't converge."
      │do
       "FunctionSpace"
        ======
        plotServ
         ( visualiseSinkhornConv @'FunctionSpace QD.fromDouble (SinkhornOTConfig 18)
               broadPeaks )
         "Broad peaks. Converges." ──
        plotServ
         ( visualiseSinkhornConv @'FunctionSpace QD.fromDouble (SinkhornOTConfig 18)
               mediumPeaks )
         "Medium peaks. Converges!" ──
        plotServ
         ( visualiseSinkhornConv @'FunctionSpace QD.fromDouble (SinkhornOTConfig 18)
               narrowPeaks )
         "Narrow peaks. Diverges." ──
        plotServ
         ( visualiseSinkhornConv @'FunctionSpace QD.fromDouble (SinkhornOTConfig 32)
               broadPeaks )
         "λ big, still converges."


useLightColourscheme :: Bool
useLightColourscheme = False

style = [cassius|
   body
     height: 96vh
     color: #{textColour}
     background: #{backgroundStyle}
     font-size: 4.3vmin
     font-family: "Linux libertine", "Times New Roman"
   .main-title
     font-size: 180%
   h1
     font-size: 150%
   div
     width: 95%
     height: 100%
     text-align: center
     margin: auto
     border-radius: 6px
     background: #{divBoxesHint}
   .global-title
     width: 70%
     font-size: 180%
     font-weight: bold
   .headed-container
     height: 80%
   .vertical-concatenation
     display: flex
     flex-direction: column
   .items-list>div
     margin-left: 0px
   .items-list>div>div, .items-list>.list-item
     display: list-item
     margin-left: 2em
     text-align: left
   .list-item
     text-align: left
   .h6
     font-weight: bold
   .emph
     font-style: italic
   .bf
     font-weight: bold
   .small
     font-size: 67%
   .verb
     display: inline-block
     font-size: 86%
     background-color: #227
     font-family: "Ubuntu Mono", "Droid Sans mono", "Courier New"
   .lightbg img
     background-color: rgba(255,255,255,1)
   .invimg img
     background-color: rgba(255,255,255,1)
     filter: invert(90%)
   .heightlimited video
     max-height: 80vh
   .still-hidden
     visibility: hidden
   .strikedOut
     opacity: 0.4
     text-decoration: line-through
   .narrow
     max-width: 40vw
   pre
     text-align: left
     font-size: 82%
     background-color: #204
     font-family: "Ubuntu Mono", "Droid Sans mono", "Courier New"
   .laweqn pre
     background-color: #422
   .reference, .cited-author
      font-variant: small-caps
   a.pseudolink
      text-decoration: underline
      color: #7090ff
  |] ()
 where backgroundStyle :: String
       backgroundStyle
        | useLightColourscheme  = "linear-gradient(#7fb, #a8f)"
        | otherwise             = "linear-gradient(#263, #516)"
       textColour :: String
       textColour
        | useLightColourscheme  = "#110"
        | otherwise             = "#ffe"
       divBoxesHint :: String
       divBoxesHint
        | useLightColourscheme  = "rgba(100,100,215,0.1)"
        | otherwise             = "rgba(0,0,15,0.1)"

items :: [Presentation] -> Presentation

items [] = " "
items bs = "items-list" #% foldr1 (──) (("list-item"#%)<$>bs)

items_p :: [Presentation] -> Presentation
items_p its = sequence_
  [ items $ v ++ map hide h
  | (v,h) <- tail $ zip (inits its) (tails its) ]

items_p' :: [(Presentation, Presentation->Presentation)] -> Presentation
items_p' its = sequence_
  [ items $ map fst (init v) ++ [fvω vω] ++ map (hide . fst) h
  | (v,h) <- tail $ zip (inits its) (tails its)
  , let (vω,fvω) = last v ]

emph :: Presentation -> Presentation
emph = ("emph"#%)

bf :: Presentation -> Presentation
bf = ("bf"#%)

h6 :: Presentation -> Presentation
h6 = ("h6"#%)

urlRef :: String -> Presentation
urlRef s = staticContent [shamlet|<a .pseudolink>#{s}|]

law :: Presentation -> Presentation
law = ("laweqn"#%)

hide :: Presentation -> Presentation
hide = hide' id

hide' :: (Presentation -> Presentation) -> Presentation -> Presentation
hide' f x = do
    "still-hidden"#%x
    "now-visible"#%f x

verb :: String -> Presentation
verb s = "verb" #% fromString s

later :: (Presentation -> Presentation) -> Presentation -> Presentation
later f c = c >> f c

striking :: Presentation -> Presentation
striking = later ("strikedOut"#%)

plotServ :: (?plotLock :: IORef (Maybe ThreadId))
         => [DynamicPlottable] -> Presentation -> Presentation
plotServ pl cont = cont >> serverSide`id`do
       locked <- readIORef ?plotLock
       case locked of
        Nothing -> do
         writeIORef ?plotLock . Just
          =<< forkFinally
               (plotWindow' (
                 if useLightColourscheme
                  then def & setSolidBackground Dia.white
                           & graphicsPostprocessing .~ Dia.fc Dia.black
                  else def  ) pl)
               (\_ -> do
                 stillLocked <- readIORef ?plotLock
                 myId <- myThreadId
                 case stillLocked of
                   Just i | i==myId
                     -> writeIORef ?plotLock Nothing )
        _ -> error "Another plot window is still open."
  >> cont

plotStat :: ViewportConfig -> [DynamicPlottable] -> Presentation
plotStat viewCfg pl = imageFromFileSupplier "png" $ \file -> do
    prerendered <- plotPrerender viewCfg pl
    Dia.renderCairo file
                    (Dia.mkSizeSpec $ Just (fromIntegral $ viewCfg^.xResV)
                               Dia.^& Just (fromIntegral $ viewCfg^.yResV))
                    prerendered

embedD¹ :: (ℝ,ℝ) -> (D¹->ℝ) -> ℝ->ℝ
embedD¹ (l,r) f x
  | x>l && x<r  = f . D¹ $ 2*(x-l)/(r-l) - 1
  | otherwise   = 0/0

haarPlot :: Haar D¹ ℝ -> DynamicPlottable
haarPlot = lineSegPlot . map (first $ \(D¹ x) -> x) . haarFunctionGraph

opac :: Double -> DynamicPlottable -> DynamicPlottable
opac = tweakPrerendered . Dia.opacity




instance AdditiveGroup QD.QuadDouble where
  zeroV = 0
  (^+^) = (+)
  (^-^) = (-)
  negateV = negate
instance VectorSpace QD.QuadDouble where
  type Scalar QD.QuadDouble = QD.QuadDouble
  (*^) = (*)
instance Semimanifold QD.QuadDouble where
  type Needle QD.QuadDouble = QD.QuadDouble
  toInterior = pure
  translateP = pure (+)
instance PseudoAffine QD.QuadDouble where
instance AffineSpace QD.QuadDouble where
  type Diff QD.QuadDouble = QD.QuadDouble
  (.-.) = (-)
  (.+^) = (+)
instance TensorSpace QD.QuadDouble where
  type TensorProduct QD.QuadDouble w = w
  linearManifoldWitness = LinearManifoldWitness BoundarylessWitness
  scalarSpaceWitness = ScalarSpaceWitness
  fmapTensor = bilinearFunction $ \(LinearFunction f) (Tensor w) -> Tensor $ f w
  scaleTensor = bilinearFunction $ \μ (Tensor w) -> Tensor $ μ*^w
  addTensors (Tensor w₀) (Tensor w₁) = Tensor $ w₀ ^+^ w₁
  negateTensor = LinearFunction $ \(Tensor w) -> Tensor $ negateV w
  zeroTensor = Tensor zeroV
  transposeTensor = LinearFunction $ \(Tensor w) -> toFlatTensor $ w
  toFlatTensor = LinearFunction Tensor
  fromFlatTensor = LinearFunction getTensorProduct
instance LinearSpace QD.QuadDouble where
  type DualVector QD.QuadDouble = QD.QuadDouble
  dualSpaceWitness = DualSpaceWitness
  applyDualVector = bilinearFunction (*^)
  applyLinear = bilinearFunction $ \(LinearMap w) μ -> w^*μ
instance FreeVectorSpace QD.QuadDouble where
  vmap = id
  (^*^) = (*)
instance Num' QD.QuadDouble where
