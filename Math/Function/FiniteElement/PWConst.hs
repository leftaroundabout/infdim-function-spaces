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


data family PWConst x y

-- | Piecewise-constant functions on the unit interval whose integral is zero.
data PWConst₀ y
       = PWConstZero
       | PWConst₀ !y           -- ^ Offset-difference between the left and right half
                  (PWConst₀ y) -- ^ Left half of the function domain
                  (PWConst₀ y) -- ^ Right half, i.e. [0.5 .. 1[.

data instance PWConst ℝ y = PWConst_ℝ
    { pwconst_ℝ_offset :: y
    , pwconst_ℝ_variation :: PWConst₀ (Diff y) }

evalPWConst_ℝ :: (AffineSpace y, VectorSpace (Diff y))
              => PWConst ℝ y -> ℝ -> y
evalPWConst_ℝ (PWConst_ℝ offs varis) x = offs .+^ evalVari varis x
 where evalVari PWConstZero _ = zeroV
       evalVari (PWConst₀ δlr lh rh) x
        | x<0.5      = evalVari lh (x*2) ^-^ δlr
        | otherwise  = evalVari lh (x*2 - 1) ^+^ δlr
