{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE UnicodeSyntax        #-}
{-# LANGUAGE DataKinds            #-}
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
import Math.Function.FiniteElement.PWLinear
import Data.VectorSpace
import Data.Manifold.Types
import Data.Semigroup
import Math.LinearMap.Category

main :: IO ()
main = defaultMain $ testGroup "Tests"
 [ testGroup "Haar sampling on real line"
  [ testProperty "Identity function" . retrieveSampledFn @'Haar
         $ \(D¹ x) -> x
  , testProperty "Quadratic function" . retrieveSampledFn @'Haar
         $ \(D¹ x) -> x^2
  , testProperty "4th-order polynomial" . retrieveSampledFn @'Haar
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
      $ \a b c d res intv@(D¹ xl, D¹ xr)
          -> let f (D¹ x) = a*x^3 + b*x^2 + c*x + d
                 ʃf (D¹ x) = a*x^4/4 + b*x^3/3 + c*x^2/2 + d*x
                 exact = ʃf (D¹ xr) - ʃf (D¹ xl)
                 haary = integrateHaarFunction (homsampleHaarFunction res f) intv
                 trapz = trapezoidal (fromInteger $ getPowerOfTwo res) (f . D¹) (xl,xr)
             in counterexample ("Analytic: "<>show exact
                                <>", Numerical: "<>show haary
                                <>", Trapezoidal: "<>show trapz)
                 $ max (magnitude (haary - exact))
                       (magnitude (trapz - exact))
                    <= 5*maximum (abs<$>[a,b,c,d])/fromIntegral (getPowerOfTwo res)
  , testProperty "Integration of random Haar function"
      $ \f (Positive res) p@(D¹ xl, D¹ xr)
          -> let trapz = trapezoidal res (evalHaarFunction f . D¹) (xl,xr)
                 haary = integrateHaarFunction f p
             in counterexample ("Trapezoidal: "<>show trapz<>", Haar: "<>show haary)
                  $ magnitude (haary - trapz)
                     <= magnitude f/(fromIntegral res*detailScale f)
  ]
 , testGroup "CHaar sampling on real interval"
  [ testProperty "Identity function" . retrieveSampledFn @'CHaar
         $ \(D¹ x) -> x
  , testProperty "Quadratic function" . retrieveSampledFn @'CHaar
         $ \(D¹ x) -> x^2
  , testProperty "4th-order polynomial" . retrieveSampledFn @'CHaar
         $ \(D¹ x) -> x^4/9 + x^3/2 - x^2/3 - x - 0.3
  ]
 ]


data FunctionSamplingScheme
  = Haar | HaarI | CHaar

class RetrievableFunctionSampling (f :: FunctionSamplingScheme) where
  type FunctionSampling f x y :: *
  homsampleFunction :: PowerOfTwo -> (D¹ -> ℝ) -> FunctionSampling f D¹ ℝ
  evalFunction :: FunctionSampling f D¹ ℝ -> D¹ -> ℝ
  allowedRelDiscrepancy :: PowerOfTwo -> ℝ

instance RetrievableFunctionSampling 'Haar where
  type FunctionSampling 'Haar x y = Haar x y
  homsampleFunction = homsampleHaarFunction
  evalFunction = evalHaarFunction
  allowedRelDiscrepancy res = 3/fromIntegral (getPowerOfTwo res)

instance RetrievableFunctionSampling 'CHaar where
  type FunctionSampling 'CHaar x y = CHaar x y
  homsampleFunction = homsampleCHaarFunction
  evalFunction = evalCHaarFunction
  allowedRelDiscrepancy res = 2/fromIntegral (getPowerOfTwo res)^2

retrieveSampledFn :: ∀ f . RetrievableFunctionSampling f
               => (D¹ -> ℝ) -> PowerOfTwo -> D¹ -> QC.Property
retrieveSampledFn f res p = counterexample
   ("Exact: "<>show exact<>", sampled: "<>show sampled<>", discrepancy: "<>show discrepancy)
    $ discrepancy <= allowedRelDiscrepancy @f res
 where sampled = (evalFunction @f)
         ((homsampleFunction @f) res f)
         p
       exact = f p
       discrepancy = abs $ sampled ^-^ exact

-- | Reference numerical calculation of integral from 0 to x.
trapezoidal :: Int -> (ℝ -> ℝ) -> (ℝ, ℝ) -> ℝ
trapezoidal n 𝑓 (𝑥l, 𝑥r)
  | 𝑥r == 𝑥l   = 0
  | 𝑥r < 𝑥l    = -trapezoidal n 𝑓 (𝑥r,𝑥l)
  | otherwise  = (𝑓 𝑥l + 𝑓 𝑥r)*ℎ/2
                  + sum [𝑓 x | x<-[𝑥l+ℎ, 𝑥l+2*ℎ .. 𝑥r-ℎ]]*ℎ
 where 𝑛 = fromIntegral n
       ℎ = (𝑥r-𝑥l)/𝑛

infix 4 ≃
(≃) :: (InnerSpace v, Scalar v ~ ℝ, Show v) => v -> v -> QC.Property
v ≃ w = counterexample
   (show v ++ " ̸≃ " ++ show w)
  $ magnitude (v^-^w) <= 1e-9 * (magnitude v + magnitude w)
