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

module Math.Function.FiniteElement.PWConst
        () where

import Data.Manifold.Types
import Data.Complex
import Data.List
import Data.AffineSpace
import Data.VectorSpace
import qualified Linear as Lin

import Control.Monad
import Control.Applicative


data family Haar x y

-- | Piecewise-constant functions on the unit interval whose integral is zero.
--   The name refers to the fact that this type effectively contains a decomposition
--   in a basis of Haar wavelets.
data Haar₀ y
       = HaarZero
       | Haar₀ !y        -- ^ Offset-amplitude between the left and right half
               (Haar₀ y) -- ^ Left half of the function domain
               (Haar₀ y) -- ^ Right half, i.e. [0.5 .. 1[.

data instance Haar D¹ y = Haar_D¹
    { pwconst_D¹_offset :: !y
    , pwconst_D¹_variation :: Haar₀ (Diff y) }

evalHaar_D¹ :: (AffineSpace y, VectorSpace (Diff y))
              => Haar D¹ y -> D¹ -> y
evalHaar_D¹ (Haar_D¹ offs varis) x = offs .+^ evalVari varis x
 where evalVari HaarZero _ = zeroV
       evalVari (Haar₀ δlr lh rh) (D¹ x)
        | x<0        = evalVari lh (D¹ $ x*2 + 1) ^-^ δlr
        | otherwise  = evalVari lh (D¹ $ x*2 - 1) ^+^ δlr

newtype PowerOfTwo = PowerOfTwo { binaryExponent :: Int } deriving (Eq, Ord, Show)

homsampleHaar_D¹ :: (AffineSpace y, Diff y ~ y, VectorSpace y, Fractional (Scalar y))
            => PowerOfTwo -> (D¹ -> y) -> Haar D¹ y
homsampleHaar_D¹ (PowerOfTwo 0) f = Haar_D¹ (f $ D¹ 0) HaarZero
homsampleHaar_D¹ (PowerOfTwo i) f
   = case homsampleHaar_D¹ (PowerOfTwo $ i-1) <$> [f . leftHalf, f . rightHalf] of
       [Haar_D¹ y₀l sfl, Haar_D¹ y₀r sfr]
        -> Haar_D¹ ((y₀l^+^y₀r)^/2) $ Haar₀ ((y₀r^-^y₀l)^/2) sfl sfr

leftHalf, rightHalf :: D¹ -> D¹
leftHalf (D¹ x) = D¹ $ (x-1)/2
rightHalf (D¹ x) = D¹ $ (x+1)/2
