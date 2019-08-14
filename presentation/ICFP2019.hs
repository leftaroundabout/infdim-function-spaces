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


main :: IO ()
main = do
 newPlotLock <- newIORef Nothing
 let ?plotLock = newPlotLock
 
 yeamer . styling style $ do
   ""──
     "global-title"#%
       "Lazy Evaluation in Infinite-Dimensional Function Spaces with Wavelet Basis"
     ──
     "Justus Sagemüller"
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

   "Why would vector=array make sense?"
    ======do
     items_p
      [do"Finite-dimensional space:"
          ──"every vector can be represented"
           <> " as weighted superposition of "<>𝑛$<>" basis vectors."
          & plotServ [ withDraggablePoints
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
                     ]
      ,do"Generalisation:"
          ──"every vector in a "<>emph"Hilbert space"
           <> " can be represented as a convergent sequence."
          -- interactive Fourier expansion
      ,do"In both cases, an orthonormal basis can reconstruct the coefficients."
      ]


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

striking :: Presentation -> Presentation
striking c = c >> "strikedOut"#%c

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

opac :: Double -> DynamicPlottable -> DynamicPlottable
opac = tweakPrerendered . Dia.opacity


