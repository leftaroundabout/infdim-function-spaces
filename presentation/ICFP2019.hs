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
import Control.Lens hiding (set)
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
   
   "Clichés: Understanding of “Functions”"
    ======do
     items
      [ h6"Maths"<>": "<>(𝑓⸪𝐴-→𝐵)$<>" maps points in set "<>𝐴$<>" to points in set "<>𝐵$<>"."
      , h6"CS"<>": "<>(𝑓°(𝑎⸪𝐴)⸪𝐵)$<>" is an algorithm that computes a result "
          <>(𝑏⸪𝐵) $<>", dependent on "<>𝑎$<>"."
      , h6"Physics"│items
         [ h6"Theoretical"<>": "
          <>(𝑓°𝑎)$<>" is an algebraic expression containing the symbol "<>𝑎$<>"."
         , h6"Experimental"<>": "
          <>(𝑓⸪𝐴-→𝐵)$<>" maps measurements in space "<>𝐴
           $<>" to predictions in space "<>𝐵$<>"."
         ]
      , h6"Data science / numerics"<>": "<>(𝑓⸪𝐴-→𝐵)$<>" is a cloud of points "<>(𝑝◞𝑖∈𝐴×𝐵)
         $<>" such that for any "<>(𝑎∈𝐴)$<>", we can interpolate between nearby points a "
         <>"value "<>(𝑏∈𝐵)$<>" in some suitable way."
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

type Distance = ℝ  -- in m
type Pos = V3 Distance
type Speed = ℝ -- in m/s
type Velo = V3 Speed
type PhaseSpace = (Pos, Velo)
type Mass = ℝ   -- in kg
type PhaseSpace_ConsE = (Pos, S²)

type T² = (S¹, S¹)

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


type ODESolver = ∀ y t . (PseudoAffine y, RealSpace (Needle y), t ~ ℝ, Interior y ~ y)
    => (y -> Needle y) -> Needle t -> (t,y) -> [(t,y)]

euler :: ODESolver
euler f h = go
 where go (t,y) = (t,y) : go (t+h, y .+~^ h · f y)

rk4 :: ODESolver
rk4 f h = go
 where go (t,y) = (t,y) : go
            (t+h, y .+~^ h/6 · (k₁ ^+^ 2·k₂ ^+^ 2·k₃ ^+^ k₄))
        where k₁ = f y
              k₂ = f $ y .+~^ h/2 · k₁
              k₃ = f $ y .+~^ h/2 · k₂
              k₄ = f $ y .+~^ h · k₃

trajectoryPlot :: Int -> [(String, Distance)] -> [[(ℝ,ℝ)]] -> DynamicPlottable
trajectoryPlot speed meta = plotLatest
    . map ( transpose . take 80 >>>
           \chunkCompos -> plotMultiple
             [ (if name/="" then legendName name else id)
              $ plot [ lineSegPlot chunkCompo
                     , shapePlot . Dia.moveTo (p2 $ last chunkCompo)
                             . Dia.opacity 0.6
                         $ Dia.circle radius ]
             | ((name,radius), chunkCompo) <- zip meta chunkCompos ]
           )
    . iterate (drop speed)

type TwoBody = (PhaseSpace, PhaseSpace)

earthMass, sunMass :: Mass
earthMass = 5.972e24  -- in kg
sunMass = 1.988e30    -- in kg

earthDist, sunRadius, earthRadius :: Distance
earthDist = 1.496e11 -- in m
sunRadius = 6.957e8 -- in m
earthRadius = 6.371e6 -- in m

earthSpeed :: Speed
earthSpeed = 29.8e3 -- in m/s

gravConst :: ℝ
gravConst = 6.674e-11  -- in N·m²/kg²

gravAcc :: Mass -> Diff Pos -> Diff Velo
gravAcc mt δx = (gravConst * mt / magnitude δx^3) · δx

traject2Body :: ODESolver -> (Mass, Mass) -> TwoBody -> [TwoBody]
traject2Body solver (me, ms) xv₀ = snd <$>
   solver (\((xe,ve), (xs,vs))
            -> ( (ve, gravAcc ms $ xs.-.xe)
               , (vs, gravAcc me $ xe.-.xs) )
               )
          120000
          (0, xv₀)

data SymplecticOperability = SymplecticWorking | BrownMotionBroken

traject1Body_ConsE :: ODESolver -> SymplecticOperability
                        -> Mass -> PhaseSpace -> [PhaseSpace_ConsE]
traject1Body_ConsE solver okness ms (x₀,v₀) = snd <$>
   solver (\(xe,veDir)
            -> let absv = sqrt $ 2*(energy - epot xe)
                   accTn:@._ = coEmbed ( gravAcc ms (negateV xe)
                                         ^/(case okness of
                                             SymplecticWorking -> absv
                                             BrownMotionBroken -> 1):@. embed veDir
                                           :: TangentBundle ℝ³ )
                                 :: TangentBundle S²
               in (absv*^embed veDir, accTn)
               )
          120000
          (0, (x₀, coEmbed v₀))
 where energy = epot x₀ + 1/2*magnitudeSq v₀
       epot x = -gravConst*ms/magnitude x

-- | A very rough globe model, representing the continents as circular blobs.
earthFn :: S² -> Dia.Colour ℝ
earthFn p
   = case [ colour
          |  (    loc   ,  size,    colour          ) <-
           [ (  90◯    0,  0.3 , Dia.aliceblue      )  -- Arctic
           , ( -90◯    0,  0.5 , Dia.aliceblue      )  -- Antarctic
           , (  48◯  -86,  0.6 , Dia.forestgreen    )  -- Asia
           , (  50◯  -15,  0.3 , Dia.darkgreen      )  -- Europe
           , (  19◯    0,  0.27, Dia.darkkhaki      )  -- northern Africa
           , (  18◯  -30,  0.32, Dia.khaki          )  -- Middle East
           , ( -13◯  -26,  0.27, Dia.forestgreen    )  -- southern Africa
           , (  46◯  100,  0.5 , Dia.darkolivegreen )  -- North America
           , (  12◯   83,  0.15, Dia.darkgreen      )  -- Middle America
           , (  -9◯   57,  0.4 , Dia.darkgreen      )  -- northern South America
           , ( -37◯   66,  0.2 , Dia.forestgreen    )  -- southern South America
           , ( -25◯ -133,  0.4 , Dia.orange         )  -- Australia
           ]
          , magnitudeSq (p.-~.loc) < size^2 ] of
        (c:_) -> c
        _     -> Dia.midnightblue
 where infix 4 ◯
       lat ◯ lon = S²Polar ((90-lat)*pi/180)
                           (  lon   *pi/180)

withInteractiveRotation :: (Rotatable r, AxisSpace r ~ ℝP²)
  => (ℝ,ℝ) -> ℝ -> ((r -> r) -> DynamicPlottable) -> DynamicPlottable
withInteractiveRotation dragOrigin sphRadius disp = plot $ \(MousePressed mouse) ->
    let (rdx,rdz) = maybe zeroV (^-^dragOrigin) mouse ^/ sphRadius
        axis
         | rdx==0     = HemisphereℝP²Polar (pi/2) (-pi/2)
         | rdx*rdz>0  = HemisphereℝP²Polar (atan $ rdz/rdx) (pi/2)
         | otherwise  = HemisphereℝP²Polar (atan $ -rdz/rdx) (-pi/2)
    in disp $ rotateAbout axis
               (S¹Polar $ magnitude(rdx,rdz) * signum rdx)
