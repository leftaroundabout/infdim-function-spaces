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

data instance Haar ℝ y = Haar_ℝ
    { pwconst_ℝ_offset :: !y
    , pwconst_ℝ_variation :: Haar₀ (Diff y) }

evalHaar_ℝ :: (AffineSpace y, VectorSpace (Diff y))
              => Haar ℝ y -> ℝ -> y
evalHaar_ℝ (Haar_ℝ offs varis) x = offs .+^ evalVari varis x
 where evalVari HaarZero _ = zeroV
       evalVari (Haar₀ δlr lh rh) x
        | x<0.5      = evalVari lh (x*2) ^-^ δlr
        | otherwise  = evalVari lh (x*2 - 1) ^+^ δlr

newtype PowerOfTwo = PowerOfTwo { binaryExponent :: Int } deriving (Eq, Ord, Show)

homsampleHaar_ℝ :: (AffineSpace y, Diff y ~ y, VectorSpace y, Fractional (Scalar y))
            => PowerOfTwo -> (ℝ -> y) -> Haar ℝ y
homsampleHaar_ℝ (PowerOfTwo 0) f = Haar_ℝ (f 0.5) HaarZero
homsampleHaar_ℝ (PowerOfTwo i) f
   = case homsampleHaar_ℝ (PowerOfTwo $ i-1) <$> [f . (/2), f . (/2).(+1)] of
       [Haar_ℝ y₀l sfl, Haar_ℝ y₀r sfr]
        -> Haar_ℝ ((y₀l^+^y₀r)^/2) $ Haar₀ ((y₀r^-^y₀l)^/2) sfl sfr
