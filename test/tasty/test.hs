{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE UnicodeSyntax        #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE AllowAmbiguousTypes  #-}

import Test.Tasty
import Test.Tasty.QuickCheck
import qualified Test.QuickCheck as QC
import Math.Function.FiniteElement.PWConst
import Data.VectorSpace
import Data.Manifold.Types
import Data.Semigroup

main :: IO ()
main = defaultMain $ testGroup "Tests"
 [ testGroup "Haar sampling on real line"
  [ testProperty "Identity function" . retrieveSampledFn
         $ \(D¹ x) -> x
  , testProperty "Quadratic function" . retrieveSampledFn
         $ \(D¹ x) -> x^2
  , testProperty "4th-order polynomial" . retrieveSampledFn
         $ \(D¹ x) -> x^4/9 + x^3/2 - x^2/3 - x - 0.3
  ]
 ]

retrieveSampledFn :: (D¹ -> ℝ) -> PowerOfTwo -> D¹ -> QC.Property
retrieveSampledFn f res p = counterexample
   ("Exact: "<>show exact<>", sampled: "<>show sampled<>", discrepancy: "<>show discrepancy)
    $ discrepancy <= 3/fromIntegral (getPowerOfTwo res)
 where sampled = evalHaarFunction
         (homsampleHaarFunction res f)
         p
       exact = f p
       discrepancy = abs $ sampled ^-^ exact

