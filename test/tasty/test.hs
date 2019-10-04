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
import Data.VectorSpace.Free
import Data.Manifold.Types
import Data.Semigroup
import Math.LinearMap.Category

import GHC.Exts (Constraint)


main :: IO ()
main = defaultMain $ testGroup "Tests"
 [ testGroup "Haar sampling on real interval"
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
  , testProperty "Multiplicativity of sampled form"
         $ \cfs₀ cfs₁ res
            -> let f (a,b,c) (D¹ x) = a*x^2 + b*x + c
                   [f₀,f₁] = f<$>[cfs₀,cfs₁]
               in homsampleHaarFunction res f₀ ^*^ homsampleHaarFunction res f₁
                    ≃ (homsampleHaarFunction res (\p->f₀ p*f₁ p) :: Haar D¹ ℝ)
  , testProperty "Point-wise function application"
         $ \(a,b,c) res
            -> let f (D¹ x) = a*x^2 + b*x + c
                   g = asinh
               in vmap g (homsampleHaarFunction res f)
                    ≃ homsampleHaarFunction res (g . f)
  ]
 , testGroup "Haar sampling on real line"
  [ testProperty "Identity function" . retrieveSampledFn @'Haar
         $ \x -> x
  , testProperty "Sine function" . retrieveSampledFn @'Haar
         $ \x -> sin x
  , testProperty "tanh of 4th-order polynomial" . retrieveSampledFn @'Haar
         $ \x -> tanh $ x^4/32 + x^3/8 - x^2/5 - x - 0.3
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
  , testProperty "Co-Riesz functionals"
      $ \f g -> (coRiesz_origReso$f)<.>^(g :: Haar D¹ ℝ) ≃ f<.>g
  , testProperty "Linearity"
      $ \f g μ h -> let f' = coRiesz$(f :: Haar D¹ ℝ)
                    in f'<.>^(g ^+^ μ*^h :: Haar D¹ ℝ)
                      ≃ f'<.>^g + μ*^(f'<.>^h)
  , testProperty "Resolution-limited Riesz isomorphism"
         $ \a b c res
             -> let f :: Haar D¹ ℝ
                    f = homsampleHaarFunction res $ \(D¹ x) -> a*x^2 + b*x + c
                in (riesz_resolimited res . coRiesz $ f) ≃ f
  , testProperty "Multiplicativity of dual vectors: identity and polynomials"
         $ \cfs₀ cfs₁ res
            -> let f (a, b, c) (D¹ x) = a*x^2 + b*x + c
                   [f₀,f₁] = homsampleHaarFunction res . f<$>[cfs₀,cfs₁] :: [Haar D¹ ℝ]
                   ι = boxDistributionD¹ (D¹ $ -1, D¹ 1) 1 :: DualVector (Haar D¹ ℝ)
               in (dualPointwiseMul f₀ $ ι) <.>^ f₁ ≃ ι <.>^ (f₀^*^f₁)
  , testProperty "Multiplicativity of dual vectors: arbitrary"
         $ \u ψ φ -> (dualPointwiseMul ψ $ u) <.>^ φ ≃ u <.>^ (ψ^*^φ)
  , testProperty "Multiplicativity of dual vectors: reciprocal"
         $ \(f :: Haar D¹ ℝ) (g :: Haar D¹ ℝ) p
              -> let f² = vmap ((+0.1).(^2)) f
                 in (dualPointwiseMul (vmap recip f²) . dualPointwiseMul f² $ p) <.>^ g
                         ≃ p<.>^g
  ]
 , testGroup "Tensors"
  [ testProperty "Bilinearity of tensor product"
      $ \(f,g :: Haar D¹ ℝ) (h,i :: Haar D¹ ℝ)
          -> (f^+^g)⊗(h^+^i) ≃ f⊗h ^+^ f⊗i ^+^ g⊗h ^+^ g⊗i
  , testProperty "Transpose tensor product"
      $ \(f :: Haar D¹ ℝ) (g :: Haar D¹ ℝ)
            -> (transposeTensor $ f⊗g) ≃ g⊗f
  , testProperty "Involution of transposition"
      $ \(t :: Haar D¹ ℝ ⊗ Haar D¹ ℝ)
            -> (transposeTensor $ transposeTensor $ t) ≃ t
  ]
 , testGroup "Linear maps"
  [ testProperty "Identity map"
      $ \f -> ((id :: Haar D¹ ℝ+>Haar D¹ ℝ) $ f) ≃ f
  ]
 , testGroup "Distributions"
  [ testProperty "Dirac evaluation of given Haar function, D¹"
      $ \f (p::D¹) -> dirac p<.>^f ≃ evalHaarFunction f p
  , testProperty "Dirac evaluation of sampled polynomial (on D¹)"
      $ \a b c d res p
          -> let f (D¹ x) = a*x^3/3 + b*x^2/2 + c*x + d
                 exact = f p
                 diracSampled = dirac p<.>^homsampleHaarFunction res f
             in counterexample ("Exact: "<>show exact<>", Dirac: "<>show diracSampled)
                 $ magnitude (diracSampled - exact)
                    <= 5*maximum (abs<$>[a,b,c,d])/fromIntegral (getPowerOfTwo res)
  , testProperty "Dirac evaluation of trig function (on ℝ)"
      $ \a b c res p'
          -> let p = asinh p' -- avoid huge values
                 f :: ℝ -> ℝ
                 f x = a*cos x + b*sin x + c
                 exact = f p
                 diracSampled = dirac p<.>^homsampleHaarFunction res f
             in counterexample ("Exact: "<>show exact<>", Dirac: "<>show diracSampled)
                 $ magnitude (diracSampled - exact)
                    <= 5*maximum (abs<$>[a,b,c])/fromIntegral (getPowerOfTwo res)
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
  , testProperty "Additivity of sampled form"
         $ \cfs₀ cfs₁ res
            -> let f (a,b,c) (D¹ x) = a*x^2 + b*x + c
                   [f₀,f₁] = f<$>[cfs₀,cfs₁]
               in homsampleCHaarFunction res f₀ ^+^ homsampleCHaarFunction res f₁
                    ≃ (homsampleCHaarFunction res (f₀^+^f₁) :: CHaar D¹ ℝ)
  ]
 , testGroup "CHaar to PWLinear conversion"
  [ testProperty "Evaluation same in both representations"
         $ \(f :: CHaar D¹ ℝ) p
           -> evalCHaarFunction f p ≃ evalBinsubPWLinear (toBinsubPWLinear f) p
  , testProperty "Addition same in both representations"
         $ \f g
           -> toBinsubPWLinear f ^+^ toBinsubPWLinear g
               ≃ toBinsubPWLinear (f^+^g :: CHaar D¹ ℝ)
  ]
 , testGroup "Vector space laws"
  [ testProperty "Commutativity of addition"
      $ \f g -> f ^+^ g ≃ (g ^+^ f :: CHaar D¹ ℝ)
  , testProperty "Associativity of addition"
      $ \f g h -> f ^+^ (g ^+^ h) ≃ ((f ^+^ g) ^+^ h :: CHaar D¹ ℝ)
  , testProperty "Distributivity"
      $ \f g μ -> μ*^(f ^+^ g :: CHaar D¹ ℝ) ≃ μ*^f ^+^ μ*^g
  ]
 , testGroup "Inner product laws"
  [ testProperty "Commutativity"
      $ \f g -> f<.>(g :: CHaar D¹ ℝ) ≃ g<.>f
  , testProperty "Bilinearity"
      $ \f g h μ -> (f^+^g)<.>(μ*^h :: CHaar D¹ ℝ)
                   ≃ μ*(f<.>h + g<.>h)
  ]
 ]


data FunctionSamplingScheme
  = Haar | HaarI | CHaar

class RetrievableFunctionSampling (f :: FunctionSamplingScheme) where
  type FunctionSampling f x y :: *
  type PermittedDomain f x :: Constraint
  homsampleFunction :: PermittedDomain f x
             => PowerOfTwo -> (x -> ℝ) -> FunctionSampling f x ℝ
  evalFunction :: PermittedDomain f x
             => FunctionSampling f x ℝ -> x -> ℝ
  allowedRelDiscrepancy :: PowerOfTwo -> ℝ

instance RetrievableFunctionSampling 'Haar where
  type FunctionSampling 'Haar x y = Haar x y
  type PermittedDomain 'Haar x = HaarSamplingDomain x
  homsampleFunction = homsampleHaarFunction
  evalFunction = evalHaarFunction
  allowedRelDiscrepancy res = 5/fromIntegral (getPowerOfTwo res)

instance RetrievableFunctionSampling 'CHaar where
  type FunctionSampling 'CHaar x y = CHaar x y
  type PermittedDomain 'CHaar x = CHaarSamplingDomain x
  homsampleFunction = homsampleCHaarFunction
  evalFunction = evalCHaarFunction
  allowedRelDiscrepancy res = 2/fromIntegral (getPowerOfTwo res)^2

retrieveSampledFn :: ∀ f x . (RetrievableFunctionSampling f, PermittedDomain f x)
               => (x -> ℝ) -> PowerOfTwo -> x -> QC.Property
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
