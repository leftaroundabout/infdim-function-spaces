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
  , testProperty "Additivity of sampled form"
         $ \cfs₀ cfs₁ res
            -> let f (a,b,c) (D¹ x) = a*x^2 + b*x + c
                   [f₀,f₁] = f<$>[cfs₀,cfs₁]
               in homsampleHaarFunction res f₀ ^+^ homsampleHaarFunction res f₁
                    ≃ (homsampleHaarFunction res (f₀^+^f₁) :: Haar D¹ ℝ)
  ]
 , testGroup "Vector space laws"
  [ testProperty "Commutativity of addition"
      $ \f g -> f ^+^ g ≃ (g ^+^ f :: Haar D¹ ℝ)
  , testProperty "Associativity of addition"
      $ \f g h -> f ^+^ (g ^+^ h) ≃ ((f ^+^ g) ^+^ h :: Haar D¹ ℝ)
  , testProperty "Distributivity"
      $ \f g μ -> μ*^(f ^+^ g :: Haar D¹ ℝ) ≃ μ*^f ^+^ μ*^g
  ]
 , testGroup "Inner product laws"
  [ testProperty "Commutativity"
      $ \f g -> f<.>(g :: Haar D¹ ℝ) ≃ g<.>f
  , testProperty "Bilinearity"
      $ \f g h μ -> (f^+^g)<.>(μ*^h :: Haar D¹ ℝ)
                   ≃ μ*(f<.>h + g<.>h)
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

infix 4 ≃
(≃) :: (InnerSpace v, Scalar v ~ ℝ, Show v) => v -> v -> QC.Property
v ≃ w = counterexample
   (show v ++ " ̸≃ " ++ show w)
  $ magnitude (v^-^w) <= 1e-9 * (magnitude v + magnitude w)
