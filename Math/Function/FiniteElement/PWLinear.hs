-- |
-- Module      : Math.Function.FiniteElement.PWLinear
-- Copyright   : (c) Justus Sagemüller 2019
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsagemue $ uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UnicodeSyntax          #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE RoleAnnotations        #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE DataKinds              #-}

module Math.Function.FiniteElement.PWLinear
       ( -- * Functions
           HaarI, HaarISamplingDomain(..)
         -- * Utility
        , PowerOfTwo(..), getPowerOfTwo, multiscaleDecompose, VAffineSpace
        ) where

import Math.Function.Duals.Meta
import Math.Function.FiniteElement.PWConst.Internal
import Math.Function.FiniteElement.Internal.Util

import Data.Manifold.Types
import Data.Manifold.PseudoAffine
import Data.Complex
import Data.List
import Data.AffineSpace
import Data.VectorSpace
import Math.LinearMap.Category
import qualified Control.Functor.Constrained as CC
import qualified Control.Arrow.Constrained as CC
import qualified Control.Applicative.Constrained as CC

import Data.Functor
import Control.Monad
import Control.Applicative
import Data.Tagged
import Data.Type.Coercion
import GHC.Generics
import Control.Lens (Prism', prism', view, re)

import qualified Test.QuickCheck as QC


-- | Piecewise-linear function with regular, power-of-two subdivisions, but
--   not necessarily with homogeneous resolution. 
--   The name refers to the fact that the derivative of these functions has a
--   decomposition in Haar wavelets, i.e. they are integrals of Haar wavelets.
type family HaarI x y

class HaarISamplingDomain x where
  evalHaarIFunction :: (VAffineSpace y, Scalar y ~ ℝ)
            => HaarI x y -> x -> y
  homsampleHaarIFunction :: (VAffineSpace y, Diff y ~ y, Fractional (Scalar y))
            => PowerOfTwo -> (x -> y) -> HaarI x y

-- | Piecewise-linear functions @f@ on the unit interval.
data HaarI_D¹ dn y = HaarI_D¹
    { haarI_D¹_center :: y
    , haarI_D¹_derivative :: Haar_D¹ dn y }
deriving instance (Show y, Show (Diff y)) => Show (HaarI_D¹ dn y)

type instance HaarI D¹ y = HaarI_D¹ FunctionSpace y

instance CC.Functor (HaarI_D¹ dn) (LinearFunction ℝ) (LinearFunction ℝ) where
  fmap = fmapLFH
   where fmapLFH :: ∀ y z . (TensorSpace y, TensorSpace z, Scalar y ~ ℝ, Scalar z ~ ℝ)
             => (y-+>z) -> (HaarI_D¹ dn y-+>HaarI_D¹ dn z)
         fmapLFH f = case (linearManifoldWitness @z, linearManifoldWitness @y) of
          (LinearManifoldWitness _, LinearManifoldWitness _) ->
           LinearFunction $
            \(HaarI_D¹ y₀ δs) -> HaarI_D¹ (f CC.$ y₀)
                      $ getLinearFunction (CC.fmap f) δs

instance CC.Monoidal (HaarI_D¹ dn) (LinearFunction ℝ) (LinearFunction ℝ) where
  pureUnit = LinearFunction $ \Origin -> zeroV
  fzipWith = fzwLFH
   where fzwLFH :: ∀ x y z dn . 
                      ( TensorSpace x, TensorSpace y, TensorSpace z
                      , Scalar x ~ ℝ, Scalar y ~ ℝ, Scalar z ~ ℝ )
                   => ((x,y)-+>z) -> ((HaarI_D¹ dn x, HaarI_D¹ dn y) -+> HaarI_D¹ dn z)
         fzwLFH = case ( linearManifoldWitness @x
                       , linearManifoldWitness @y
                       , linearManifoldWitness @z ) of
          (LinearManifoldWitness _, LinearManifoldWitness _, LinearManifoldWitness _)
             -> \f -> LinearFunction
                   $ \(HaarI_D¹ x δxs, HaarI_D¹ y δys)
                        -> HaarI_D¹ (f CC.$ (x,y))
                                   (getLinearFunction (CC.fzipWith f) (δxs,δys))
         
evalHaarI_D¹ :: (VAffineSpace y, Scalar y ~ ℝ) => HaarI D¹ y -> D¹ -> y
evalHaarI_D¹ (HaarI_D¹ y₀ fluct) x = y₀ .+^ integrateHaarFunction fluct (D¹ 0, x)

instance HaarISamplingDomain D¹ where
  evalHaarIFunction = evalHaarI_D¹


instance (VAffineSpace y) => AffineSpace (HaarI_D¹ dn y) where
  type Diff (HaarI_D¹ dn y) = HaarI_D¹ dn (Diff y)
  HaarI_D¹ y₀ δ₀ .+^ HaarI_D¹ y₁ δ₁ = HaarI_D¹ (y₀.+^y₁) (δ₀.+^δ₁)
  HaarI_D¹ y₀ δ₀ .-. HaarI_D¹ y₁ δ₁ = HaarI_D¹ (y₀.-.y₁) (δ₀.-.δ₁)

instance (VAffineSpace y, Diff y ~ y, AdditiveGroup y)
             => AdditiveGroup (HaarI_D¹ dn y) where
  zeroV = HaarI_D¹ zeroV zeroV
  (^+^) = (.+^)
  (^-^) = (.-.)
  negateV (HaarI_D¹ y δ) = HaarI_D¹ (negateV y) (negateV δ)

instance (VectorSpace y, AffineSpace y, Diff y ~ y)
             => VectorSpace (HaarI_D¹ dn y) where
  type Scalar (HaarI_D¹ dn y) = Scalar y
  μ *^ HaarI_D¹ y δ = HaarI_D¹ (μ*^y) (μ*^δ)

instance ( VAffineSpace y
         , Semimanifold y, Needle y ~ Diff y
         , Semimanifold (Diff y), Needle (Diff y) ~ Diff y )
             => Semimanifold (HaarI_D¹ dn y) where
  type Needle (HaarI_D¹ dn y) = HaarI_D¹ dn (Needle y)
  type Interior (HaarI_D¹ dn y) = HaarI_D¹ dn y
  translateP = Tagged (.+^)
  toInterior = Just
  fromInterior = id
instance ( VAffineSpace y
         , Semimanifold y, Needle y ~ Diff y
         , Semimanifold (Diff y), Needle (Diff y) ~ Diff y )
             => PseudoAffine (HaarI_D¹ dn y) where
  (.-~!) = (.-.)

instance ∀ y dn
         . (TensorSpace y, AffineSpace y, Diff y ~ y, Needle y ~ y, Scalar y ~ ℝ)
             => TensorSpace (HaarI_D¹ dn y) where
  type TensorProduct (HaarI_D¹ dn y) w = HaarI_D¹ dn (y⊗w)
  wellDefinedVector (HaarI_D¹ y₀ δs)
       = HaarI_D¹ <$> wellDefinedVector y₀ <*> wellDefinedVector δs
  wellDefinedTensor (Tensor (HaarI_D¹ y₀ δs))
       = Tensor <$> (HaarI_D¹ <$> wellDefinedVector y₀ <*> wellDefinedVector δs)
  scalarSpaceWitness = case scalarSpaceWitness :: ScalarSpaceWitness y of
     ScalarSpaceWitness -> ScalarSpaceWitness
  linearManifoldWitness = case linearManifoldWitness :: LinearManifoldWitness y of
     LinearManifoldWitness BoundarylessWitness -> LinearManifoldWitness BoundarylessWitness
  coerceFmapTensorProduct = cftlp
   where cftlp :: ∀ a b p . p (HaarI_D¹ dn y) -> Coercion a b
                   -> Coercion (HaarI_D¹ dn (Tensor ℝ (Diff y) a))
                               (HaarI_D¹ dn (Tensor ℝ (Diff y) b))
         cftlp _ c = case CC.fmap c :: Coercion (Tensor ℝ y a) (Tensor ℝ y b) of
            Coercion -> Coercion
  zeroTensor = zeroV
  toFlatTensor = LinearFunction Tensor CC.. CC.fmap toFlatTensor
  fromFlatTensor = CC.fmap fromFlatTensor CC.. LinearFunction getTensorProduct
  addTensors (Tensor f) (Tensor g) = Tensor $ f^+^g
  scaleTensor = bilinearFunction $ \μ (Tensor f) -> Tensor $ μ*^f
  negateTensor = LinearFunction $ \(Tensor f) -> Tensor $ negateV f
  tensorProduct = bilinearFunction
         $ \f w -> Tensor $ CC.fmap (LinearFunction $ \y -> y⊗w) CC.$ f
  transposeTensor = LinearFunction $
       \(Tensor (HaarI_D¹ yw₀ δs))
           -> (CC.fmap (LinearFunction $ (`HaarI_D¹`zeroV)) CC.. transposeTensor CC.$ yw₀)
  fmapTensor = bilinearFunction $ \a (Tensor f)
             -> Tensor $ CC.fmap (CC.fmap a) CC.$ f
  fzipTensorWith = bilinearFunction $ \a (Tensor f, Tensor g)
             -> Tensor $ CC.fzipWith (getLinearFunction fzipTensorWith a) CC.$ (f,g)



instance ∀ y dn . ( LinearSpace y, AffineSpace y
                  , Diff y ~ y, Needle y ~ y, Scalar y ~ ℝ
                  , Diff (DualVector y) ~ DualVector y, Needle (DualVector y) ~ DualVector y
                  , AffineSpace (DualVector y)
                  , ValidDualness dn )
             => LinearSpace (HaarI_D¹ dn y) where
  type DualVector (HaarI_D¹ dn y) = HaarI_D¹ (Dual dn) (DualVector y)
  dualSpaceWitness = case ( dualSpaceWitness :: DualSpaceWitness y
                          , dualityWitness :: DualityWitness dn ) of
       (DualSpaceWitness, DualityWitness) -> DualSpaceWitness
  linearId = LinearMap hId
   where hId = case dualSpaceWitness :: DualSpaceWitness y of
          DualSpaceWitness
            -> HaarI_D¹ (case linearId :: y+>y of
                        LinearMap yId
                            -> CC.fmap (LinearFunction
                                             $ \y -> HaarI_D¹ y zeroV)
                                         CC.$ (Tensor yId :: DualVector y⊗y))
                       (CC.fmap (CC.fmap . LinearFunction
                                          $ \δs -> HaarI_D¹ zeroV δs) CC.$ getLinearMap
                                              (linearId :: Haar_D¹ dn y+>Haar_D¹ dn y))
  tensorId = LinearMap $ hId
   where hId :: ∀ w . (LinearSpace w, Scalar w ~ ℝ)
               => HaarI_D¹ (Dual dn)
                    (Tensor (Scalar (DualVector y))
                            (DualVector y)
                            (Tensor Double (DualVector w) (Tensor ℝ (HaarI_D¹ dn y) w)))
         hId = case ( dualSpaceWitness :: DualSpaceWitness y
                    , dualSpaceWitness :: DualSpaceWitness w ) of
          (DualSpaceWitness, DualSpaceWitness)
            -> HaarI_D¹ (case tensorId :: (y⊗w)+>(y⊗w) of
                        LinearMap ywId
                            -> CC.fmap (CC.fmap $ LinearFunction
                                          $ \yw -> Tensor $ HaarI_D¹ yw zeroV)
                                       CC.$ (undefined -- Tensor ywId
                                              :: DualVector y⊗(DualVector w⊗(y⊗w))))
                       (case tensorId :: (Haar_D¹ dn y⊗w)+>(Haar_D¹ dn y⊗w) of
                          LinearMap h₀ywId
                           -> CC.fmap (CC.fmap . CC.fmap . LinearFunction
                                       $ \(Tensor q) -> Tensor (HaarI_D¹ zeroV q))
                                 CC.$ h₀ywId)
  applyDualVector = bilinearFunction $ \(HaarI_D¹ a₀ δa) (HaarI_D¹ f₀ δf)
      -> case dualSpaceWitness :: DualSpaceWitness y of
           DualSpaceWitness -> (getLinearFunction applyDualVector a₀ CC.$ f₀)
                             + (getLinearFunction applyDualVector δa CC.$ δf)
  applyTensorFunctional = bilinearFunction $ \(LinearMap a) (Tensor f) -> go a f
   where go :: ∀ u . (LinearSpace u, Scalar u ~ ℝ)
             => HaarI_D¹ (Dual dn) (DualVector y⊗DualVector u) -> HaarI_D¹ dn (y⊗u) -> ℝ
         go (HaarI_D¹ (Tensor a₀) δa) (HaarI_D¹ f₀ δf)
          = case ( dualSpaceWitness :: DualSpaceWitness y
                 , dualSpaceWitness :: DualSpaceWitness u ) of
           (DualSpaceWitness, DualSpaceWitness)
               -> (getLinearFunction applyDualVector (LinearMap a₀ :: y+>DualVector u)
                                                              CC.$ f₀)
                + (getLinearFunction applyDualVector
                              (Coercion CC.$ δa) CC.$ δf)
  applyLinear = bilinearFunction $ \(LinearMap a) f -> go a f
   where go :: ∀ w . (TensorSpace w, Scalar w ~ ℝ)
                => HaarI_D¹ (Dual dn) (Tensor (Scalar (DualVector y)) (DualVector y) w)
                      -> HaarI_D¹ dn y -> w
         go (HaarI_D¹ (Tensor a₀) δa) (HaarI_D¹ f₀ δf)
           = ( (getLinearFunction applyLinear (LinearMap a₀ :: y+>w)) CC.$ f₀ )
          ^+^ ( getLinearFunction applyLinear (LinearMap δa :: Haar_D¹ dn y+>w) CC.$ δf )
  applyTensorLinMap = bilinearFunction $ \(LinearMap a) (Tensor f) -> go a f
   where go :: ∀ u w . (LinearSpace u, Scalar u ~ ℝ, TensorSpace w, Scalar w ~ ℝ)
                => HaarI_D¹ (Dual dn) (Tensor
                           (Scalar (DualVector y))
                            (DualVector y)
                            (Tensor Double (DualVector u) w))
                 -> HaarI_D¹ dn (y⊗u) -> w
         go (HaarI_D¹ (Tensor a₀) δa) (HaarI_D¹ f₀ δf)
               = ( (getLinearFunction applyTensorLinMap
                          (LinearMap a₀ :: (y⊗u)+>w)) CC.$ f₀ )
              ^+^ ( (getLinearFunction applyTensorLinMap $ LinearMap δa)
                              CC.$ (Tensor δf :: Haar_D¹ dn y⊗u) )

instance (QC.Arbitrary y, QC.Arbitrary (Diff y))
               => QC.Arbitrary (HaarI_D¹ FunctionSpace y) where
  arbitrary = HaarI_D¹ <$> QC.arbitrary <*> QC.arbitrary
           

