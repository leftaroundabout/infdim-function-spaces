-- |
-- Module      : Math.Function.Duals.Meta
-- Copyright   : (c) Justus Sagemüller 2019
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsagemue $ uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}

module Math.Function.Duals.Meta
       ( Dualness(..), Dual, DualityWitness(..), ValidDualness(..)
        ) where



data Dualness = FunctionSpace | DistributionSpace

type family Dual (dn :: Dualness) where
  Dual FunctionSpace = DistributionSpace
  Dual DistributionSpace = FunctionSpace


data DualityWitness (dn :: Dualness) where
  DualityWitness :: (ValidDualness (Dual dn), Dual (Dual dn) ~ dn)
           => DualityWitness dn
class ValidDualness (dn :: Dualness) where
  dualityWitness :: DualityWitness dn
instance ValidDualness FunctionSpace where dualityWitness = DualityWitness
instance ValidDualness DistributionSpace where dualityWitness = DualityWitness

