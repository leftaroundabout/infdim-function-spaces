-- |
-- Module      : Math.Function.FiniteElement.PWConst
-- Copyright   : (c) Justus Sagemüller 2019
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsagemue $ uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE UnicodeSyntax         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Math.Function.FiniteElement.PWConst
       ( -- * Functions
           Haar, HaarSamplingDomain(evalHaarFunction, homsampleHaarFunction)
         -- * Distributions
        , dirac, boxDistributionD¹
         -- * Calculus
        , integrateHaarFunction
         -- * Utility
        , PowerOfTwo(..), getPowerOfTwo, multiscaleDecompose, haarFunctionGraph
        , VAffineSpace, detailScale, riesz_resolimited
         -- * Misc, unstable
        , dualPointwiseMul
        ) where

import Math.Function.FiniteElement.PWConst.Internal
import Math.Function.FiniteElement.Internal.Util
import Math.Function.Duals.Meta

import Data.Tagged

import Data.Manifold.PseudoAffine
import Data.Manifold.Types
import Data.VectorSpace
import Data.VectorSpace.Free
import Data.AffineSpace
import Math.LinearMap.Category

import Data.Type.Coercion

import qualified Prelude
import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained


instance ( FreeVectorSpace y, VAffineSpace y
         , TensorSpace y, Needle y ~ y, Scalar y ~ ℝ )
                => FreeVectorSpace (Haar_D¹ 'FunctionSpace y) where
  
  Haar_D¹ c₀ HaarZero ^*^ Haar_D¹ c₁ HaarZero = Haar_D¹ (c₀^*^c₁) HaarZero
  Haar_D¹ c HaarZero ^*^ f = fmap (LinearFunction (c^*^)) $ f
  f ^*^ Haar_D¹ c HaarZero = fmap (LinearFunction (^*^c)) $ f
  Haar_D¹ c₀ (HaarUnbiased δ₀ f₀l f₀r) ^*^ Haar_D¹ c₁ (HaarUnbiased δ₁ f₁l f₁r)
      = case ( Haar_D¹ (c₀^-^δ₀) f₀l ^*^ Haar_D¹ (c₁^-^δ₁) f₁l
             , Haar_D¹ (c₀^+^δ₀) f₀r ^*^ Haar_D¹ (c₁^+^δ₁) f₁r ) of
         (Haar_D¹ cl fl, Haar_D¹ cr fr)
           -> Haar_D¹ ((cl^+^cr)^/2) $ HaarUnbiased ((cr^-^cl)^/2) fl fr
  
  vmap f (Haar_D¹ c HaarZero) = Haar_D¹ (vmap f c) HaarZero
  vmap f (Haar_D¹ c (HaarUnbiased δ fl fr))
     = case ( vmap f (Haar_D¹ (c^-^δ) fl), vmap f (Haar_D¹ (c^+^δ) fr) ) of
         (Haar_D¹ cl fl, Haar_D¹ cr fr)
           -> Haar_D¹ ((cl^+^cr)^/2) $ HaarUnbiased ((cr^-^cl)^/2) fl fr
         
dualPointwiseMul :: Haar_D¹ FunctionSpace ℝ
          -> Haar_D¹ DistributionSpace ℝ -> Haar_D¹ DistributionSpace ℝ
dualPointwiseMul (Haar_D¹ c₀ HaarZero) (Haar_D¹ c₁ HaarZero)
       = Haar_D¹ (c₀*c₁) HaarZero
dualPointwiseMul (Haar_D¹ c HaarZero) f
           = fmap (LinearFunction (c*)) $ f
dualPointwiseMul f (Haar_D¹ c HaarZero)
           = dualPointwiseMul f $ Haar_D¹ c (HaarUnbiased zeroV zeroV zeroV)
dualPointwiseMul (Haar_D¹ c₀ (HaarUnbiased δ₀ f₀l f₀r))
                 (Haar_D¹ c₁ (HaarUnbiased δ₁ f₁l f₁r))
      = case ( dualPointwiseMul (Haar_D¹ (c₀^-^δ₀) f₀l) (Haar_D¹ ((c₁^-^δ₁)^/2) f₁l)
             , dualPointwiseMul (Haar_D¹ (c₀^+^δ₀) f₀r) (Haar_D¹ ((c₁^+^δ₁)^/2) f₁r) ) of
         (Haar_D¹ cl fl, Haar_D¹ cr fr)
           -> Haar_D¹ (cl^+^cr) $ HaarUnbiased (cr^-^cl) fl fr



data Haar_ℝ dn y = Haar_ℝ
  { hℝ_leftExtensions :: [Haar_D¹ dn y]
  , hℝ_minus1to1 :: Haar_D¹ dn y
  , hℝ_rightExtensions :: [Haar_D¹ dn y]
  }

type instance Haar ℝ y = Haar_ℝ 'FunctionSpace y

instance HaarSamplingDomain ℝ where
  evalHaarFunction (Haar_ℝ _ c _) x
   | x > -1 && x < 1   = evalHaarFunction c $ D¹ x
  evalHaarFunction (Haar_ℝ (l:ls) _ _) x
   | x < -1            = evalHaarFunction (Haar_ℝ ls l []) $ (x+3)/2
  evalHaarFunction (Haar_ℝ _ _ (r:rs)) x
   | x > 1             = evalHaarFunction (Haar_ℝ [] r rs) $ (x-3)/2
  evalHaarFunction _ _ = zeroV
  
  homsampleHaarFunction reso@(TwoToThe p) f
    = case homsampleHaarFunction (TwoToThe $ p+1)
             <$> [f . subtract 3 . (*2), f . (+3) . (*2)] of
       ~[Haar_ℝ ls l _, Haar_ℝ _ r rs]
        -> Haar_ℝ (l:ls)
                  (homsampleHaarFunction reso $ \(D¹ x) -> f x)
                  (r:rs)
  
  dirac p = boxDistributionℝ (p,p) 1

boxDistributionℝ :: (VAffineSpace y, Scalar y ~ ℝ)
                     => (ℝ, ℝ) -> y -> Haar_ℝ DistributionSpace y
boxDistributionℝ (l, r) y
  | l > r            = boxDistributionℝ (r, l) y
  | l >= -1, r <= 1  = Haar_ℝ [] (boxDistributionD¹ (D¹ l, D¹ r) y) []
  | l >= 1           = case boxDistributionℝ ((l-3)/2, (r-3)/2) y of
                        Haar_ℝ _ dc dr -> Haar_ℝ [] zeroV (dc : dr)
  | r <= -1          = case boxDistributionℝ ((l+3)/2, (r+3)/2) y of
                        Haar_ℝ dl dc _ -> Haar_ℝ (dc : dl) zeroV []
  | l >= -1          = let bl = (1-l)/(r-l)
                       in boxDistributionℝ (l,1) (y^*bl)
                            ^+^ boxDistributionℝ (1,r) (y^*(1-bl))
  | otherwise        = let bl = (-1-l)/(r-l)
                       in boxDistributionℝ (l,-1) (y^*bl)
                            ^+^ boxDistributionℝ (-1,r) (y^*(1-bl))

zipAddWith :: (AdditiveGroup v, AdditiveGroup w)
                 => (v->w->x) -> [v] -> [w] -> [x]
zipAddWith f [] rs = (zeroV`f`) <$> rs
zipAddWith f ls [] = (`f`zeroV) <$> ls
zipAddWith f (l:ls) (r:rs) = (f l r) : zipAddWith f ls rs

zipAdd :: AdditiveGroup v => [v] -> [v] -> [v]
zipAdd [] rs = rs
zipAdd ls [] = ls
zipAdd (l:ls) (r:rs) = (l^+^r) : zipAdd ls rs

instance (VAffineSpace y, Diff y ~ y, AdditiveGroup y)
           => AdditiveGroup (Haar_ℝ dn y) where
  zeroV = Haar_ℝ [] zeroV []
  negateV (Haar_ℝ l c r) = Haar_ℝ (negateV<$>l) (negateV c) (negateV<$>r)
  Haar_ℝ l₀ c₀ r₀ ^+^ Haar_ℝ l₁ c₁ r₁
    = Haar_ℝ (zipAdd l₀ l₁) (c₀^+^c₁) (zipAdd r₀ r₁)

instance (VAffineSpace y, Diff y ~ y, AdditiveGroup y)
           => AffineSpace (Haar_ℝ dn y) where
  type Diff (Haar_ℝ dn y) = Haar_ℝ dn y
  (.+^) = (^+^)
  (.-.) = (^-^)

instance (VAffineSpace y, Diff y ~ y, AdditiveGroup y)
           => VectorSpace (Haar_ℝ dn y) where
  type Scalar (Haar_ℝ dn y) = Scalar y
  μ *^ Haar_ℝ l c r = Haar_ℝ ((μ*^)<$>l) (μ*^c) ((μ*^)<$>r)

instance ( VAffineSpace y
         , Semimanifold y, Needle y ~ Diff y
         , Semimanifold (Diff y), Needle (Diff y) ~ Diff y )
             => Semimanifold (Haar_ℝ dn y) where
  type Needle (Haar_ℝ dn y) = Haar_ℝ dn (Needle y)
  type Interior (Haar_ℝ dn y) = Haar_ℝ dn y
  translateP = Tagged (.+^)
  toInterior = Just
  fromInterior = id
instance ( VAffineSpace y
         , Semimanifold y, Needle y ~ Diff y
         , Semimanifold (Diff y), Needle (Diff y) ~ Diff y )
             => PseudoAffine (Haar_ℝ dn y) where
  (.-~!) = (.-.)

instance Functor (Haar_ℝ dn) (LinearFunction ℝ) (LinearFunction ℝ) where
  fmap = fmapLFH
   where fmapLFH :: ∀ y z . (TensorSpace y, TensorSpace z, Scalar y ~ ℝ, Scalar z ~ ℝ)
             => (y-+>z) -> (Haar_ℝ dn y-+>Haar_ℝ dn z)
         fmapLFH f = case (linearManifoldWitness @z, linearManifoldWitness @y) of
          (LinearManifoldWitness _, LinearManifoldWitness _) ->
           LinearFunction $
            \(Haar_ℝ l c r) -> Haar_ℝ
               (map (fmap f $) l) (fmap f $ c) (map (fmap f $) r)
instance Monoidal (Haar_ℝ dn) (LinearFunction ℝ) (LinearFunction ℝ) where
  pureUnit = LinearFunction $ \Origin -> zeroV
  fzipWith = fzwLFH
   where fzwLFH :: ∀ x y z dn .
                      ( TensorSpace x, TensorSpace y, TensorSpace z
                      , Scalar x ~ ℝ, Scalar y ~ ℝ, Scalar z ~ ℝ )
                   => ((x,y)-+>z) -> ((Haar_ℝ dn x, Haar_ℝ dn y) -+> Haar_ℝ dn z)
         fzwLFH = case ( linearManifoldWitness @x
                       , linearManifoldWitness @y
                       , linearManifoldWitness @z ) of
          (LinearManifoldWitness _, LinearManifoldWitness _, LinearManifoldWitness _)
             -> \f -> LinearFunction
                   $ \(Haar_ℝ lx cx rx, Haar_ℝ ly cy ry)
                        -> Haar_ℝ [ fzipWith f $ (x,y)
                                  | (x,y)<-zipAddWith (,) lx ly ]
                                  (fzipWith f $ (cx,cy))
                                  [ fzipWith f $ (x,y)
                                  | (x,y)<-zipAddWith (,) rx ry ]

instance ∀ y dn . (TensorSpace y, AffineSpace y, Diff y ~ y, Needle y ~ y, Scalar y ~ ℝ)
              => TensorSpace (Haar_ℝ dn y) where
  type TensorProduct (Haar_ℝ dn y) w = Haar_ℝ dn (y⊗w)
  wellDefinedVector = undefined
  wellDefinedTensor = undefined
  scalarSpaceWitness = case scalarSpaceWitness @(Haar_D¹ dn y) of
        ScalarSpaceWitness -> ScalarSpaceWitness
  coerceFmapTensorProduct = cftlp
   where cftlp :: ∀ a b p . p (Haar_ℝ dn y) -> Coercion a b
                   -> Coercion (Haar_ℝ dn (Tensor ℝ (Diff y) a))
                               (Haar_ℝ dn (Tensor ℝ (Diff y) b))
         cftlp _ c = case fmap c :: Coercion (Tensor ℝ y a) (Tensor ℝ y b) of
            Coercion -> Coercion
  linearManifoldWitness = case linearManifoldWitness :: LinearManifoldWitness y of
     LinearManifoldWitness BoundarylessWitness -> LinearManifoldWitness BoundarylessWitness
  zeroTensor = Tensor $ Haar_ℝ [] zeroV []
  toFlatTensor = LinearFunction Tensor . fmap toFlatTensor
  fromFlatTensor = fmap fromFlatTensor . LinearFunction getTensorProduct
  addTensors (Tensor l) (Tensor r) = Tensor $ l^+^r
  scaleTensor = bilinearFunction (*^)
  negateTensor = LinearFunction $ Tensor . negateV . getTensorProduct
  tensorProduct = bilinearFunction
      $ \f w -> Tensor $ fmap (LinearFunction $ \y -> y⊗w) $ f
  transposeTensor = LinearFunction
       $ \(Tensor (Haar_ℝ l c r)) -> 
            sumV [ fmap (LinearFunction`id`\lb'
                                -> Haar_ℝ (replicate i zeroV++[lb']) zeroV [])
                        . transposeTensor $ Tensor lb
                 | (i,lb) <- zip [0..] l ]
        ^+^ (fmap (LinearFunction `id` \c' -> Haar_ℝ [] c' [])
                  . transposeTensor $ Tensor c)
        ^+^ sumV [ fmap (LinearFunction`id`\rb'
                                -> Haar_ℝ [] zeroV (replicate i zeroV++[rb']))
                        . transposeTensor $ Tensor rb
                 | (i,rb) <- zip [0..] r ]
  fmapTensor = bilinearFunction
         $ \a (Tensor f) -> Tensor $ fmap (fmap a) $ f
  fzipTensorWith = bilinearFunction $ \a (Tensor f, Tensor g)
        -> Tensor $ fzipWith (getLinearFunction fzipTensorWith a) $ (f,g)



instance ∀ y dn . ( LinearSpace y, AffineSpace y
                  , Diff y ~ y, Needle y ~ y, Scalar y ~ ℝ
                  , Diff (DualVector y) ~ DualVector y, Needle (DualVector y) ~ DualVector y
                  , AffineSpace (DualVector y), ValidDualness dn )
              => LinearSpace (Haar_ℝ dn y) where
  type DualVector (Haar_ℝ dn y) = Haar_ℝ (Dual dn) (DualVector y)
  dualSpaceWitness = case ( dualSpaceWitness :: DualSpaceWitness y
                          , dualityWitness :: DualityWitness dn ) of
       (DualSpaceWitness, DualityWitness) -> DualSpaceWitness
  linearId = LinearMap $ case ( dualSpaceWitness :: DualSpaceWitness y
                              , linearId :: Haar_D¹ dn y +> Haar_D¹ dn y ) of
      (DualSpaceWitness, LinearMap hD¹id) -> Haar_ℝ
                  [ (fmap (fmap (LinearFunction $ \l'
                                 -> Haar_ℝ (replicate i zeroV++[l']) zeroV []))
                       $ hD¹id)
                  | i <- [0..] ]
                  (fmap (fmap (LinearFunction $ \c' -> Haar_ℝ [] c' [])) $ hD¹id)
                  [ (fmap (fmap (LinearFunction $ \r'
                                 -> Haar_ℝ [] zeroV (replicate i zeroV++[r'])))
                       $ hD¹id)
                  | i <- [0..] ]
  tensorId = LinearMap $ hId
   where hId :: ∀ w . (LinearSpace w, Scalar w ~ ℝ)
               => Haar_ℝ (Dual dn)
                    (Tensor (Scalar (DualVector y))
                            (DualVector y)
                            (Tensor ℝ (DualVector w) (Tensor ℝ (Haar_ℝ dn y) w)))
         hId = case ( dualSpaceWitness :: DualSpaceWitness y
                    , dualSpaceWitness :: DualSpaceWitness w
                    , tensorId :: (Haar_D¹ dn y⊗w)+>(Haar_D¹ dn y⊗w) ) of
          (DualSpaceWitness, DualSpaceWitness, LinearMap hD¹w_id) -> Haar_ℝ 
                  [ (fmap (fmap . fmap . LinearFunction $ \(Tensor l')
                        -> Tensor $ Haar_ℝ (replicate i zeroV++[l']) zeroV [])
                       $ hD¹w_id)
                  | i <- [0..] ]
                  (fmap (fmap . fmap . LinearFunction
                        $ \(Tensor c') -> Tensor $ Haar_ℝ [] c' []) $ hD¹w_id)
                  [ (fmap (fmap . fmap . LinearFunction $ \(Tensor r')
                        -> Tensor $ Haar_ℝ [] zeroV (replicate i zeroV++[r']))
                       $ hD¹w_id)
                  | i <- [0..] ]
  applyDualVector = bilinearFunction $ \(Haar_ℝ al ac ar) (Haar_ℝ fl fc fr)
      -> case dualSpaceWitness :: DualSpaceWitness y of
           DualSpaceWitness ->
                sum [ getLinearFunction applyDualVector a $ f
                    | (a,f) <- (ac,fc) : zip al fl ++ zip ar fr ]
  applyTensorFunctional = bilinearFunction $ \(LinearMap a) (Tensor f) -> go a f
   where go :: ∀ u . (LinearSpace u, Scalar u ~ ℝ)
             => Haar_ℝ (Dual dn) (DualVector y⊗DualVector u) -> Haar_ℝ dn (y⊗u) -> ℝ
         go (Haar_ℝ al ac ar) (Haar_ℝ fl fc fr)
          = case dualSpaceWitness :: DualSpaceWitness u of
            DualSpaceWitness
               -> sum [ getLinearFunction applyDualVector (Coercion $ a) $ f
                      | (a,f) <- (ac,fc) : zip al fl ++ zip ar fr ]
  applyLinear = bilinearFunction $ \(LinearMap a) f -> go a f
   where go :: ∀ w . (TensorSpace w, Scalar w ~ ℝ)
                => Haar_ℝ (Dual dn) (Tensor (Scalar (DualVector y)) (DualVector y) w)
                      -> Haar_ℝ dn y -> w
         go (Haar_ℝ al ac ar) (Haar_ℝ fl fc fr)
          = sumV
              [ getLinearFunction applyLinear (LinearMap a :: Haar_D¹ dn y+>w) $ f
              | (a,f) <- (ac,fc) : zip al fl ++ zip ar fr ]
  applyTensorLinMap = bilinearFunction $ \(LinearMap a) (Tensor f) -> go a f
   where go :: ∀ u w . (LinearSpace u, Scalar u ~ ℝ, TensorSpace w, Scalar w ~ ℝ)
                => Haar_ℝ (Dual dn) (Tensor
                           (Scalar (DualVector y))
                            (DualVector y)
                            (Tensor Double (DualVector u) w))
                 -> Haar_ℝ dn (y⊗u) -> w
         go (Haar_ℝ al ac ar) (Haar_ℝ fl fc fr)
           = sumV [ (getLinearFunction applyTensorLinMap $ LinearMap a)
                              $ (Tensor f :: Haar_D¹ dn y⊗u)
                  | (a,f) <- (ac,fc) : zip al fl ++ zip ar fr ]

riesz_resolimited :: PowerOfTwo -> (DualVector (Haar D¹ Double) -+> Haar D¹ Double)
riesz_resolimited res = LinearFunction $ \(Haar_D¹ c₀ f)
                           -> Haar_D¹ (c₀^/2) $ go res (1/2) f 
 where go (TwoToThe n) μ (HaarUnbiased δ l r)
        | n > 0     = HaarUnbiased (μ*^δ)
                       (go (TwoToThe $ n-1) (μ*2) l) (go (TwoToThe $ n-1) (μ*2) r)
       go _ _ _ = HaarZero

data SinkhornOTConfig = SinkhornOTConfig
  { _entropyLim_λ :: ℝ
  , _max_Sinkhorniters :: Int }

-- | Calculation of an approximately optimal (i.e. minimum earth-mover distance)
--   transport (i.e. joint distribution that has the two given marginals).
--   Uses the Sinkhorn algorithm as presented in
--   <http://papers.nips.cc/paper/4927-sinkhorn-distances-lightspeed-computation-of-optimal-transport Cuturi 2013>.
entropyLimOptimalTransport :: SinkhornOTConfig
                     -> Haar D¹ ℝ -> Haar D¹ ℝ -> Haar D¹ ℝ ⊗ Haar D¹ ℝ
entropyLimOptimalTransport (SinkhornOTConfig λ maxIters) r c = sinkh 0 smearedDiag
 where sinkh i m
         | i < maxIters  = sinkh (i+1)
                 . transpose_setLMarginal c . transpose_setLMarginal r $ m
         | otherwise     = m
       transpose_setLMarginal :: Haar D¹ ℝ -> Haar D¹ ℝ ⊗ Haar D¹ ℝ -> Haar D¹ ℝ ⊗ Haar D¹ ℝ
       transpose_setLMarginal p m
          = fmap (LinearFunction $ \w -> w^*^ρ) . transposeTensor $ m
        where p' = lMarginal m
              ρ = p^*^vmap recip p'
       smearedDiag :: Haar D¹ ℝ ⊗ Haar D¹ ℝ
       smearedDiag = Tensor . homsampleHaarFunction reso
           $ \(D¹ x) -> Tensor . homsampleHaarFunction reso
            $ \(D¹ x') -> exp $ -λ*abs (x-x')
        where reso = (TwoToThe . round $ log λ + 2)

lMarginal :: Haar D¹ Double ⊗ Haar D¹ Double -> Haar D¹ Double
lMarginal m = fromFlatTensor . fmap integrate $ m
 where integrate :: Haar D¹ ℝ -+> ℝ
       integrate = LinearFunction $ (Haar_D¹ 1 zeroV<.>^)
