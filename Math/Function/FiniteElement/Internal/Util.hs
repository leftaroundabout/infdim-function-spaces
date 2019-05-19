-- |
-- Module      : Math.Function.FiniteElement.Internal.Util
-- Copyright   : (c) Justus Sagemüller 2019
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsagemue $ uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE TypeFamilies           #-}

module Math.Function.FiniteElement.Internal.Util where

import Data.VectorSpace
import Data.AffineSpace
import Data.Manifold.Types

import Control.Lens
import Data.Functor
import Control.Applicative
import Control.Monad

-- | This constraint should in principle be just `AffineSpace`, but this conflicts
--   with the way the 'TensorSpace' class is set up, so we instead require
--   a vector space.
-- 
--   Ideally, the functions should ultimately be generalised to work even on
--   'PseudoAffine' manifolds.
type VAffineSpace y = (AffineSpace y, VectorSpace (Diff y), Diff y ~ y)

newtype PowerOfTwo = TwoToThe { binaryExponent :: Int } deriving (Eq, Ord, Show)
getPowerOfTwo :: PowerOfTwo -> Integer
getPowerOfTwo (TwoToThe ex) = 2^ex

leftHalf, rightHalf :: Prism' D¹ D¹
leftHalf  = prism' (\(D¹ x) -> D¹ $ (x-1)/2)
                   (\(D¹ x) -> guard (x<=0) $> D¹ (x*2 + 1))
rightHalf = prism' (\(D¹ x) -> D¹ $ (x+1)/2)
                   (\(D¹ x) -> guard (x>=0) $> D¹ (x*2 - 1))
