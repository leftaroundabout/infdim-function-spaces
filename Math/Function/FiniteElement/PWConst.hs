-- |
-- Module      : Math.Function.FiniteElement.PWConst
-- Copyright   : (c) Justus Sagemüller 2019
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsagemue $ uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE DataKinds         #-}

module Math.Function.FiniteElement.PWConst
       ( -- * Functions
           Haar, HaarSamplingDomain(..)
         -- * Distributions
        , dirac, boxDistribution
         -- * Calculus
        , integrateHaarFunction
         -- * Utility
        , PowerOfTwo(..), getPowerOfTwo, multiscaleDecompose, VAffineSpace, detailScale
        ) where

import Math.Function.FiniteElement.PWConst.Internal
import Math.Function.FiniteElement.Internal.Util
import Math.Function.Duals.Meta

import Data.Manifold.Types
import Data.VectorSpace


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
