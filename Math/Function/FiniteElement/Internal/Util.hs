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
{-# LANGUAGE LambdaCase             #-}

module Math.Function.FiniteElement.Internal.Util where

import Data.VectorSpace
import Data.AffineSpace
import Data.Manifold.Types

import Control.Lens

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
leftHalf  = halves . _Left
rightHalf = halves . _Right

halves :: Iso' D¹ (Either D¹ D¹)
halves = iso (\(D¹ x) -> if x < 0 then Left  . D¹ $ x*2 + 1
                                  else Right . D¹ $ x*2 - 1)
             (\case Left  (D¹ x) -> D¹ $ (x-1)/2
                    Right (D¹ x) -> D¹ $ (x+1)/2)
