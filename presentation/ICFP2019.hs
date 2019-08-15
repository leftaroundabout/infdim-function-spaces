-- This work is licensed under the Creative Commons Attribution-NoDerivatives
-- 4.0 International License.
-- To view a copy of this license, visit http://creativecommons.org/licenses/by-nd/4.0/
-- or send a letter to Creative Commons, PO Box 1866, Mountain View, CA 94042, USA.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE ImplicitParams    #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE Rank2Types        #-}
{-# LANGUAGE UnicodeSyntax     #-}
{-# LANGUAGE LambdaCase        #-}

import Presentation.Yeamer
import Presentation.Yeamer.Maths
import qualified Math.LaTeX.Prelude as LaTeX
import Math.LaTeX.StringLiterals
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

import qualified Text.Show.Pragmatic as SP

import Math.Function.FiniteElement.PWConst
import Math.Function.FiniteElement.PWLinear


main :: IO ()
main = do
 newPlotLock <- newIORef Nothing
 let ?plotLock = newPlotLock
 
 yeamer . styling style $ do
   ""──
     "global-title"#%
       "Lazy Evaluation in Infinite-Dimensional Function Spaces with Wavelet Basis"
     ──
     "Justus Sagemüller, Olivier Verdier"
     ──
     "reference"#%("Western Norway University of Applied Science")
   
-- "Clichés: Understanding of “Functions”"
--  ======do
--   items
--    [ h6"Maths"<>": "<>(𝑓⸪𝐴-→𝐵)$<>" maps points in set "<>𝐴$<>" to points in set "<>𝐵$<>"."
--    , h6"CS"<>": "<>(𝑓°(𝑎⸪𝐴)⸪𝐵)$<>" is an algorithm that computes a result "
--        <>(𝑏⸪𝐵) $<>", dependent on "<>𝑎$<>"."
--    , h6"Physics"│items
--       [ h6"Theoretical"<>": "
--        <>(𝑓°𝑎)$<>" is an algebraic expression containing the symbol "<>𝑎$<>"."
--       , h6"Experimental"<>": "
--        <>(𝑓⸪𝐴-→𝐵)$<>" maps measurements in space "<>𝐴
--         $<>" to predictions in space "<>𝐵$<>"."
--       ]
--    , h6"Data science / numerics"<>": "<>(𝑓⸪𝐴-→𝐵)$<>" is a cloud of points "<>(𝑝◞𝑖∈𝐴×𝐵)
--       $<>" such that for any "<>(𝑎∈𝐴)$<>", we can interpolate between nearby points a "
--       <>"value "<>(𝑏∈𝐵)$<>" in some suitable way."
--    ]

   "Strong opinions – for stronger types"
    ======do
     ("A vector is "<>bf"not")
      │items
       [ "An array of numbers"
       , "A monad (or, representable functor)"
       ]
      ━━""
      ━━("A vector "<>bf"is")
       │items
       [ "An element of some vector space"
       , "...that represents a set of interesting entities"
          ──items
           [ "Points/displacements in physical space"
           , "Functions or distributions" ]
       ]

   let plotPartialSums fPl tgt sqce
           = plotServ [ continFnPlot tgt
                      , startFrozen $ plotLatest
                         [ plotDelay 0.05 $ fPl (h^+^μ*^u)<>fPl (μ*^u)
                                 <> mconcat [ tweakPrerendered (Dia.opacity (exp $ -t/2))
                                               $ fPl uO
                                            | (t,uO) <- zip [1..] hist ]
                         | ((h,u),(velo,hist))
                             <- zip (zip psums sqce)
                                    (zip (tanh<$>[0.05,0.07..]) hists)
                         , μ <- [0,velo..1-velo/2] ] ]
        where psums = scanl (^+^) zeroV sqce
              hDepth = 3
              hists = map reverse
                       $ take hDepth (inits sqce)
                        ++ map (take hDepth) (tails sqce)

   let fExample x = (sin (2.7*x) + sin (7.9*x))^3 + tanh (cos $ 4*x)
       fExample_H = homsampleHaarFunction (TwoToThe 8) $ \(D¹ x) -> fExample x

   "Why would vector=array make sense?"
    ======do
     items_p'
      [ ("Finite-dimensional space:"
          ──"every vector can be represented"
           <> " as weighted superposition of "<>𝑛$<>" basis vectors."
        , plotServ [ withDraggablePoints
                        [(1,0), (0,1), (0.1,0.1)]
                        (\[e₀@(x₀,y₀),e₁@(x₁,y₁),v] -> 
                          let (e₀',e₁') = ((y₁,-x₁),(-y₀,x₀))
                                          ^/ (x₀*y₁-x₁*y₀)
                              [v₀,v₁] = (<.>v) <$> [e₀',e₁']
                              strong = Dia.lwO 3
                              weak = Dia.dashingO [5,5] 0
                          in plotMultiple [ plot [
                               shapePlot (
                                  sty $ Dia.arrowBetween (Dia.p2 r) (Dia.p2 t) )
                               | (t,r,sty) <- grp ]
                                 & legendName lgn
                              | (grp,lgn)
                                  <- [ ( [ (e₀    , zeroV , strong  )
                                         , (e₀^*v₀, zeroV , weak) ], "𝐞₀" )
                                     , ( [ (e₁    , zeroV , strong  )
                                         , (v     , e₀^*v₀, weak) ], "𝐞₁" )
                                     , ( [ (v     , zeroV , strong  ) ]
                                       , printf "%.1g·𝐞₀ + %.1g·𝐞₁" v₀ v₁ )
                                     ]
                              ]
                        )
                     , dynamicAxes
                     ] )
      , ("Generalisation:"
          ──"every vector in a "<>emph"Hilbert space"
           <> " (with Schauder basis) can be represented as a convergent sequence."
        , let basis  -- Fourier
               = homsampleHaarFunction (TwoToThe 0) (\(D¹ _) -> 1/sqrt 2)
                 : [ homsampleHaarFunction
                      (TwoToThe . max 8 . round . (+5) $ logBase 2 n)
                      $ \(D¹ x) -> tf (pi*n*x)
                   | n <- [1..]
                   , tf <- [cos, sin] ]
                     :: [Haar D¹ ℝ]
              fExample_H_coefs = (<.>fExample_H) <$> basis
          in plotPartialSums haarPlot fExample $ zipWith (*^) fExample_H_coefs basis )
      , ("In both cases, an orthonormal basis can reconstruct the coefficients."
        , id)
      ]

   "Function spaces naïvely"
    ======do
     "“Superposition of point peaks”?"
      ── items_p'
      [ ("No convergence, most points in domain are never hit."
        , let splPoints = [D¹ $ (sin x^3 + sin x)/2 | x <- [0..]]
              pseudoPointReso = 16
          in plotPartialSums haarPlot fExample
               [ getLinearFunction (riesz_resolimited $ TwoToThe pseudoPointReso)
                   $ dirac p ^* (fExample x / 2^(pseudoPointReso-1))
               | p@(D¹ x) <- splPoints ]
        )
      , ("Finite-width kernel: convergence, but limited resolution."
        , let n = 8
              r = 1/(2*n)
              splPoints = [D¹ x | x <- [r-1,2*r-1..1-r]]
          in plotPartialSums (\f -> continFnPlot $ evalCHaarFunction f . D¹) fExample
               [ homsampleCHaarFunction (TwoToThe 10)
                  $ \(D¹ x) -> let d = abs $ x-x₀
                               in if d < r then (1-(d/r))*fExample x₀
                                           else 0
               | p@(D¹ x₀) <- splPoints ]
        )
      ]

   "Why does “limited resolution” make sense?"
    ======
     do"Continuity picture"
        ======do
         "A sufficiently smooth function will deviate little within"
            <>" the resolution limit."
          ┃ maths [[𝑓°(𝑥±δ) ∈ 𝑓°𝑥 ± ε]] ""
     ──
     do let t𝑥 = tilde%$>𝑥
        "Integration picture"
         ======do
         "Pointwise evaluation is less important (or even physically meaningful)"
            <>" than integration over whole small intervals."
          ┃ maths [[𝑓°𝑥 ≈ 1/(2*δ)*(𝑥-δ,𝑥+δ)∫ d t𝑥 (𝑓°t𝑥) ]] ""
      
   "Progressively decomposing a function"
    ======
    do
     maths
      [[ 𝑓◞(𝑦◞0، 𝑓◞"l"، 𝑓◞"r")°𝑥
         ⩵ 𝑦◞0 + cases
            [ (𝑓◞"l"°𝑥◞"l", "if "<>𝑥 LaTeX.$<>" on left")
            , (𝑓◞"r"°𝑥◞"r", "if "<>𝑥 LaTeX.$<>" on right") ]
       ]]""
      & later`id`
       let f (D¹ x) = fExample x + 3
           fHaar = homsampleHaarFunction (TwoToThe 10) f
           goProg xc w doml domr fvw
             | w > domr-doml  = plotMultiple
                [ continFnPlot (embedD¹ (doml,domr) $ evalHaarFunction fvw)
                , continFnPlot (embedD¹ (doml,domr) f₀)
                , mempty
                , continFnPlot (embedD¹ (doml,domm)
                                      $ evalHaarFunction fl)
                , continFnPlot (embedD¹ (domm,domr)
                                      $ evalHaarFunction fr) ]
             | xc < domm      = goProg xc w doml domm fl
             | otherwise      = goProg xc w domm domr fr
            where (y₀, (fl, fr)) = multiscaleDecompose fvw
                  f₀ _ = y₀
                  domm = (doml+domr)/2
       in plotServ
          [ plot (\(ViewXCenter xc) (ViewWidth w) -> goProg xc w (-1) 1 fHaar)
          , mempty  & legendName "𝑓"
          , mempty  & legendName "𝑦₀"
          , mempty
          , mempty  & legendName "𝑓l"
          , mempty  & legendName "𝑓r"
          , xAxisLabel "𝑥"
          , yAxisLabel "𝑓(𝑥)" ]
    ━━do
     [plaintext|
      data PreIntg_D¹ y = PreIntg
         { offset :: y
         , lSubstructure :: PreIntg_D¹ y
         , rSubstructure :: PreIntg_D¹ y
         }
      |]│[plaintext|
      evalPreIntg_D¹ :: AdditiveGroup y
           => PreIntg_D¹ y -> D¹ -> y
      evalPreIntg_D¹ (PreIntg y0 l r) x
         = y0 + if x < 0
                 then evalPreIntg_D¹ l (2*x+1)
                 else evalPreIntg_D¹ r (2*x-1)
      |]
     [plaintext|
      data PreIntg_D¹ y
            = PreIntgZero
            | PreIntg !y !(PreIntg_D¹ y)
                         !(PreIntg_D¹ y)
      |]│[plaintext|
      evalPreIntg_D¹ :: AdditiveGroup y
           => PreIntg_D¹ y -> D¹ -> y
      evalPreIntg_D¹ PreIntgZero _ = 0
      evalPreIntg_D¹ (PreIntg y0 l r) x
         = y0 + if x < 0
                 then evalPreIntg_D¹ l (2*x+1)
                 else evalPreIntg_D¹ r (2*x-1)
      |]
      
   "De-biasing: Haar wavelets"
    ======
    do
     let δ𝑦lr = δ⁀𝑦◞"lr"
     maths
      [[ 𝑓◞(δ𝑦lr، 𝑓◞"l"، 𝑓◞"r")°𝑥
         ⩵ cases
            [ (𝑓◞"l"°𝑥◞"l" - δ𝑦lr, "if "<>𝑥 LaTeX.$<>" on left")
            , (𝑓◞"r"°𝑥◞"r" + δ𝑦lr, "if "<>𝑥 LaTeX.$<>" on right") ]
       ]]""
      & later`id`
       let f (D¹ x) = fExample x + 3
           fHaar = homsampleHaarFunction (TwoToThe 10) f
           goProg xc w doml domr fvw
             | w > domr-doml  = plotMultiple
                [ continFnPlot (embedD¹ (doml,domr) $ evalHaarFunction fvw)
                , continFnPlot (embedD¹ (doml,domr) f₀)
                , continFnPlot (embedD¹ (doml,domr) $ \(D¹ x)
                               -> if x<0 then -δlr else δlr)
                , continFnPlot (embedD¹ (doml,domm) $ (+δlr)
                                   . evalHaarFunction fl)
                , continFnPlot (embedD¹ (domm,domr) $ subtract δlr
                                   . evalHaarFunction fr) ]
             | xc < domm      = goProg xc w doml domm $ fl ^+^ cδlr
             | otherwise      = goProg xc w domm domr $ fr ^-^ cδlr
            where (y₀, (fl, fr)) = multiscaleDecompose fvw
                  f₀ _ = y₀
                  δlr = (fst (multiscaleDecompose fr) - fst (multiscaleDecompose fl))/2
                  domm = (doml+domr)/2
                  cδlr = homsampleHaarFunction (TwoToThe 1) (const δlr :: D¹->ℝ)
       in plotServ
          [ plot (\(ViewXCenter xc) (ViewWidth w) -> goProg xc w (-1) 1 fHaar)
          , mempty  & legendName "𝑓"
          , mempty  & legendName "𝑦₀"
          , mempty  & legendName "δ𝑦lr"
          , mempty  & legendName "𝑓l"
          , mempty  & legendName "𝑓r"
          , xAxisLabel "𝑥"
          , yAxisLabel "𝑓(𝑥)" ]
    ━━do
     [plaintext|
     data HaarUnbiased y
          = HaarZero
          | HaarUnbiased !y !(HaarUnbiased y)
                            !(HaarUnbiased y)
      |]│[plaintext|
     data Haar_D¹ y = Haar_D¹
         { global_offset :: !y
         , variation :: HaarUnbiased y }
      |]
     
   "Integration / sampling" 
    ======
    do
     "The offset-value requires an integral."
      <>" This needs in practice to be calculated numerically."
      <>maths [[
           (𝐷◝1)◞∫ d 𝑥 (𝑓°𝑥) ≈ 𝑖◞∑ (𝑤◞𝑖 * 𝑓°(𝑥◞𝑖)) ]]""
      ━━"For recursive subdivisions:"
       <>maths [
            [ (𝐷◝1)◞∫ d 𝑥 (𝑓°𝑥) ⩵  1/2*(𝐷◝1)◞∫ d 𝑥 (𝑓°((𝑥-1)/2)) ]
          , [                 "" + 1/2*(𝐷◝1)◞∫ d 𝑥 (𝑓°((𝑥+1)/2)) ]
             ]""
    │[plaintext|
homsampleHaar_D¹ ::
  ( VectorSpace y, Fractional (Scalar y) )
    => PowerOfTwo -> (D¹ -> y) -> Haar_D¹ y
homsampleHaar_D¹ (TwoToThe 0) f
   = Haar_D¹ (f 0) HaarZero
homsampleHaar_D¹ (TwoToThe i) f
   = case homsampleHaar_D¹ (TwoToThe $ i-1)
            <$> [ f . \x -> (x-1)/2
                , f . \x -> (x+1)/2 ] of
       [Haar_D¹ y0l sfl, Haar_D¹ y0r sfr]
        -> Haar_D¹ ((y0l+y0r)/2)
             $ HaarUnbiased ((y0r-y0l)/2)
                            sfl sfr
           |]


style = [cassius|
   body
     height: 96vh
     color: #ffe
     background: linear-gradient(#263, #516)
     font-size: 4.4vmin
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
     background: rgba(0,0,15,0.1);
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
   pre
     text-align: left
     font-size: 86%
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
plotServ pl cont = serverSide`id`do
       locked <- readIORef ?plotLock
       case locked of
        Nothing -> do
         writeIORef ?plotLock . Just
          =<< forkFinally
               (plotWindow pl)
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


