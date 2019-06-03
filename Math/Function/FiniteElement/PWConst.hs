-- |
-- Module      : Math.Function.FiniteElement.PWConst
-- Copyright   : (c) Justus Sagemüller 2019
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsagemue $ uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 

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

