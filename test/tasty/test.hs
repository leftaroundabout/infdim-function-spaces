{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE UnicodeSyntax        #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE AllowAmbiguousTypes  #-}

import qualified Prelude as Hask
import Control.Category.Constrained.Prelude

import Test.Tasty
import Test.Tasty.QuickCheck
import qualified Test.QuickCheck as QC
import Math.Function.FiniteElement.PWConst
import Data.VectorSpace
import Data.Manifold.Types
import Data.Semigroup
import Math.LinearMap.Category

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
 , testGroup "Dual space of 𝓛² Hilbert space"
  [ testProperty "Co-Riesz functionals"
      $ \f g -> (coRiesz$f)<.>^(g :: Haar D¹ ℝ) ≃ f<.>g
  , testProperty "Linearity"
      $ \f g μ h -> let f' = coRiesz$(f :: Haar D¹ ℝ)
                    in f'<.>^(g ^+^ μ*^h :: Haar D¹ ℝ)
                      ≃ f'<.>^g + μ*^(f'<.>^h)
  ]
 , testGroup "Linear maps"
  [ testProperty "Identity map"
      $ \f -> ((id :: Haar D¹ ℝ+>Haar D¹ ℝ) $ f) ≃ f
  ]
 , testGroup "Distributions"
  [ testProperty "Dirac evaluation of given Haar function"
      $ \f p -> dirac p<.>^f ≃ evalHaarFunction f p
  , testProperty "Dirac evaluation of sampled polynomial"
      $ \a b c d res p
          -> let f (D¹ x) = a*x^3/3 + b*x^2/2 + c*x + d
                 exact = f p
                 diracSampled = dirac p<.>^homsampleHaarFunction res f
             in counterexample ("Exact: "<>show exact<>", Dirac: "<>show diracSampled)
                 $ magnitude (diracSampled - exact)
                    <= 5*maximum (abs<$>[a,b,c,d])/fromIntegral (getPowerOfTwo res)
  ]
 , testGroup "Calculus"
  [ testProperty "Integration of polynomial"
      $ \a b c d res p@(D¹ xp)
          -> let f (D¹ x) = a*x^3 + b*x^2 + c*x + d
                 ʃf (D¹ x) = a*x^4/4 + b*x^3/3 + c*x^2/2 + d*x
                 exact = ʃf p
                 haary = integrateHaarFunction (homsampleHaarFunction res f) p
                 trapz = trapezoidal (fromInteger $ getPowerOfTwo res) (f . D¹) xp
             in counterexample ("Analytic: "<>show exact
                                <>", Numerical: "<>show haary
                                <>", Trapezoidal: "<>show trapz)
                 $ max (magnitude (haary - exact))
                       (magnitude (trapz - exact))
                    <= 5*maximum (abs<$>[a,b,c,d])/fromIntegral (getPowerOfTwo res)
  , testProperty "Integration of random Haar function"
      $ \f (Positive res) p@(D¹ x)
          -> let trapz = trapezoidal res (evalHaarFunction f . D¹) x
                 haary = integrateHaarFunction f p
             in counterexample ("Trapezoidal: "<>show trapz<>", Haar: "<>show haary)
                  $ magnitude (haary - trapz)
                     <= 30*magnitude f/fromIntegral res
                    
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

-- | Reference numerical calculation of integral from 0 to x.
trapezoidal :: Int -> (ℝ -> ℝ) -> ℝ -> ℝ
trapezoidal n 𝑓 𝑥t
  | 𝑥t < 0     = -trapezoidal n (𝑓 . negate) (negate 𝑥t)
  | otherwise  = (𝑓 0 + 𝑓 𝑥t)/(2*𝑛) + sum [𝑓 x | x<-[1/𝑛, 2/𝑛 .. 𝑥t]]^/𝑛
 where 𝑛 = fromIntegral n

infix 4 ≃
(≃) :: (InnerSpace v, Scalar v ~ ℝ, Show v) => v -> v -> QC.Property
v ≃ w = counterexample
   (show v ++ " ̸≃ " ++ show w)
  $ magnitude (v^-^w) <= 1e-9 * (magnitude v + magnitude w)
