-- |
-- Module      : Math.Function.FiniteElement.PWConst
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
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE UndecidableInstances   #-}

module Math.Function.FiniteElement.PWConst
        ( Haar, HaarSamplingDomain(..)
         -- * Utility
        , PowerOfTwo, getPowerOfTwo
        ) where

import Data.Manifold.Types
import Data.Manifold.PseudoAffine
import Data.Complex
import Data.List
import Data.AffineSpace
import Data.VectorSpace
import qualified Linear as Lin

import Control.Monad
import Control.Applicative
import Data.Tagged

import qualified Test.QuickCheck as QC


-- | Piecewise-constant function with regular, power-of-two subdivisions, but
--   not necessarily with homogeneous resolution. 
--   The name refers to the fact that this type effectively contains a decomposition
--   in a basis of Haar wavelets.
data family Haar x y

type VAffineSpace y = (AffineSpace y, VectorSpace (Diff y), AffineSpace (Diff y), Diff (Diff y) ~ Diff y)

class HaarSamplingDomain x where
  evalHaarFunction :: VAffineSpace y
            => Haar x y -> x -> y
  homsampleHaarFunction :: (VAffineSpace y, Diff y ~ y, Fractional (Scalar y))
            => PowerOfTwo -> (x -> y) -> Haar x y

-- | Piecewise-constant functions on the unit interval whose integral is zero.
data Haar₀ y
       = HaarZero
       | Haar₀ !y        -- ^ Offset-amplitude between the left and right half
               (Haar₀ y) -- ^ Left half of the function domain
               (Haar₀ y) -- ^ Right half, i.e. [0.5 .. 1[.
 deriving (Show)

data instance Haar D¹ y = Haar_D¹
    { pwconst_D¹_offset :: !y
    , pwconst_D¹_variation :: Haar₀ (Diff y) }
deriving instance (Show y, Show (Diff y)) => Show (Haar D¹ y)

evalHaar_D¹ :: VAffineSpace y => Haar D¹ y -> D¹ -> y
evalHaar_D¹ (Haar_D¹ offs varis) x = offs .+^ evalVari varis x
 where evalVari HaarZero _ = zeroV
       evalVari (Haar₀ δlr lh rh) (D¹ x)
        | x<0        = evalVari lh (D¹ $ x*2 + 1) ^-^ δlr
        | otherwise  = evalVari rh (D¹ $ x*2 - 1) ^+^ δlr

newtype PowerOfTwo = TwoToThe { binaryExponent :: Int } deriving (Eq, Ord, Show)
getPowerOfTwo :: PowerOfTwo -> Integer
getPowerOfTwo (TwoToThe ex) = 2^ex

homsampleHaar_D¹ :: (VAffineSpace y, Diff y ~ y, Fractional (Scalar y))
            => PowerOfTwo -> (D¹ -> y) -> Haar D¹ y
homsampleHaar_D¹ (TwoToThe 0) f = Haar_D¹ (f $ D¹ 0) HaarZero
homsampleHaar_D¹ (TwoToThe i) f
   = case homsampleHaar_D¹ (TwoToThe $ i-1) <$> [f . leftHalf, f . rightHalf] of
       [Haar_D¹ y₀l sfl, Haar_D¹ y₀r sfr]
        -> Haar_D¹ ((y₀l^+^y₀r)^/2) $ Haar₀ ((y₀r^-^y₀l)^/2) sfl sfr

leftHalf, rightHalf :: D¹ -> D¹
leftHalf (D¹ x) = D¹ $ (x-1)/2
rightHalf (D¹ x) = D¹ $ (x+1)/2

instance HaarSamplingDomain D¹ where
  evalHaarFunction = evalHaar_D¹
  homsampleHaarFunction = homsampleHaar_D¹


instance QC.Arbitrary PowerOfTwo where
  arbitrary = do
    QC.Positive i <- QC.arbitrary
    return . TwoToThe . ceiling . logBase 2 $ fromInteger i
  shrink (TwoToThe i) = TwoToThe <$> [0 .. i-1]

instance AdditiveGroup y => AffineSpace (Haar₀ y) where
  type Diff (Haar₀ y) = Haar₀ y
  HaarZero .+^ f = f
  f .+^ HaarZero = f
  Haar₀ δlr₀ δsl₀ δsr₀ .+^ Haar₀ δlr₁ δsl₁ δsr₁
            = Haar₀ (δlr₀^+^δlr₁) (δsl₀.+^δsl₁) (δsr₀.+^δsr₁)
  HaarZero .-. HaarZero = HaarZero
  Haar₀ δlr₀ δsl₀ δsr₀ .-. Haar₀ δlr₁ δsl₁ δsr₁
            = Haar₀ (δlr₀^-^δlr₁) (δsl₀.-.δsl₁) (δsr₀.-.δsr₁)

instance AdditiveGroup y => AdditiveGroup (Haar₀ y) where
  (^+^) = (.+^)
  (^-^) = (.-.)
  zeroV = HaarZero
  negateV HaarZero = HaarZero
  negateV (Haar₀ δlr δsl δsr) = Haar₀ (negateV δlr) (negateV δsl) (negateV δsr)

instance VectorSpace y => VectorSpace (Haar₀ y) where
  type Scalar (Haar₀ y) = Scalar y
  _ *^ HaarZero = HaarZero
  μ *^ Haar₀ δlr δsl δsr = Haar₀ (μ*^δlr) (μ*^δsl) (μ*^δsr)
  
instance (VAffineSpace y) => AffineSpace (Haar D¹ y) where
  type Diff (Haar D¹ y) = Haar D¹ (Diff y)
  Haar_D¹ y₀ δ₀ .+^ Haar_D¹ y₁ δ₁ = Haar_D¹ (y₀.+^y₁) (δ₀.+^δ₁)
  Haar_D¹ y₀ δ₀ .-. Haar_D¹ y₁ δ₁ = Haar_D¹ (y₀.-.y₁) (δ₀.-.δ₁)

instance (VAffineSpace y, Diff y ~ y, AdditiveGroup y)
             => AdditiveGroup (Haar D¹ y) where
  zeroV = Haar_D¹ zeroV zeroV
  (^+^) = (.+^)
  (^-^) = (.-.)
  negateV (Haar_D¹ y δ) = Haar_D¹ (negateV y) (negateV δ)

instance (VectorSpace y, AffineSpace y, Diff y ~ y)
             => VectorSpace (Haar D¹ y) where
  type Scalar (Haar D¹ y) = Scalar y
  μ *^ Haar_D¹ y δ = Haar_D¹ (μ*^y) (μ*^δ)

instance (InnerSpace y, Fractional (Scalar y)) => InnerSpace (Haar₀ y) where
  HaarZero <.> _ = 0
  _ <.> HaarZero = 0
  Haar₀ δlr₀ δsl₀ δsr₀ <.> Haar₀ δlr₁ δsl₁ δsr₁
            = δlr₀<.>δlr₁ + (δsl₀<.>δsl₁)/2 + (δsr₀<.>δsr₁)/2

-- | 𝓛² product on [-1…1] functions, i.e. @𝑓<.>𝑔 ⩵ ₋₁∫¹ d𝑥 𝑓(𝑥)·𝑔(𝑥)@
instance (InnerSpace y, Fractional (Scalar y), AffineSpace y, Diff y ~ y)
             => InnerSpace (Haar D¹ y) where
  Haar_D¹ y₀ δ₀ <.> Haar_D¹ y₁ δ₁ = 2*(y₀<.>y₁ + δ₀<.>δ₁)

instance ( VAffineSpace y
         , Semimanifold y, Needle y ~ Diff y
         , Semimanifold (Diff y), Needle (Diff y) ~ Diff y )
             => Semimanifold (Haar D¹ y) where
  type Needle (Haar D¹ y) = Haar D¹ (Needle y)
  type Interior (Haar D¹ y) = Haar D¹ y
  translateP = Tagged (.+~^)
  toInterior = Just
  fromInterior = id
instance ( VAffineSpace y
         , Semimanifold y, Needle y ~ Diff y
         , Semimanifold (Diff y), Needle (Diff y) ~ Diff y )
             => PseudoAffine (Haar D¹ y) where
  (.-~!) = (.-.)

instance (QC.Arbitrary y, QC.Arbitrary (Diff y))
               => QC.Arbitrary (Haar D¹ y) where
  arbitrary = do
     n <- QC.getSize
          -- Magic numbers for the termination-probability: chosen empirically
          -- to get both approximately n as the expectation of the number of nodes
          -- in the function's tree representation, and a reasonable variance.
     Haar_D¹ <$> QC.arbitrary <*> genΔs (round . (*3) . (**0.22) $ fromIntegral n)
   where genΔs p'¹Terminate = QC.frequency
           [ (1, pure HaarZero)
           , (p'¹Terminate, Haar₀ <$> QC.arbitrary <*> genΔs pNext <*> genΔs pNext) ]
          where pNext = floor $ fromIntegral p'¹Terminate / 1.1
           
