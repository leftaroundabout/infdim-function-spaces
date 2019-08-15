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
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE UnicodeSyntax          #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE KindSignatures         #-}

module Math.Function.Duals.Meta
       ( Dualness(..), Dual, DualityWitness(..), ValidDualness(..)
       , usingAnyDualness
        ) where



data Dualness = FunctionSpace | DistributionSpace

type family Dual (dn :: Dualness) where
  Dual FunctionSpace = DistributionSpace
  Dual DistributionSpace = FunctionSpace


data DualityWitness (dn :: Dualness) where
  DualityWitness :: (ValidDualness (Dual dn), Dual (Dual dn) ~ dn)
           => DualityWitness dn

data DualnessSingletons (dn :: Dualness) where
  FunctionnessWitness :: DualnessSingletons FunctionSpace
  DistributionnessWitness :: DualnessSingletons DistributionSpace

class ValidDualness (dn :: Dualness) where
  dualityWitness :: DualityWitness dn
  decideDualness :: DualnessSingletons dn
instance ValidDualness FunctionSpace where
  dualityWitness = DualityWitness
  decideDualness = FunctionnessWitness
instance ValidDualness DistributionSpace where
  dualityWitness = DualityWitness
  decideDualness = DistributionnessWitness

usingAnyDualness :: ∀ rc dn . ValidDualness dn
          => (rc 'FunctionSpace)
          -> (rc 'DistributionSpace)
          -> rc dn
usingAnyDualness fnCase diCase = case decideDualness @dn of
     FunctionnessWitness -> fnCase
     DistributionnessWitness -> diCase
