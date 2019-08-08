-- |
-- Module      : Math.Function.FiniteElement.PWConst
-- Copyright   : (c) Justus Sagemüller 2019
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsagemue $ uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE TypeOperators         #-}

module Math.Function.FiniteElement.PWConst
       ( -- * Functions
           Haar, HaarSamplingDomain(..)
         -- * Distributions
        , dirac, boxDistribution
         -- * Calculus
        , integrateHaarFunction
         -- * Utility
        , PowerOfTwo(..), getPowerOfTwo, multiscaleDecompose, haarFunctionGraph
        , VAffineSpace, detailScale, riesz_resolimited
        ) where

import Math.Function.FiniteElement.PWConst.Internal
import Math.Function.FiniteElement.Internal.Util

import Data.Manifold.Types
import Data.VectorSpace
import Math.LinearMap.Category


riesz_resolimited :: PowerOfTwo -> (DualVector (Haar D¹ Double) -+> Haar D¹ Double)
riesz_resolimited res = LinearFunction $ \(Haar_D¹ c₀ f)
                           -> Haar_D¹ (c₀^/2) $ go res (1/2) f 
 where go (TwoToThe n) μ (HaarUnbiased δ l r)
        | n > 0     = HaarUnbiased (μ*^δ)
                       (go (TwoToThe $ n-1) (μ*2) l) (go (TwoToThe $ n-1) (μ*2) r)
       go _ _ _ = HaarZero
