-- |
-- Module      : Math.Function.FiniteElement.PWConst.Internal
-- Copyright   : (c) Justus Sagemüller 2019
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsagemue $ uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UnicodeSyntax          #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE RoleAnnotations        #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE CPP                    #-}

module Math.Function.FiniteElement.PWConst.Internal where

import Math.Function.Duals.Meta
import Math.Function.FiniteElement.Internal.Util

import Data.Manifold.Types
import Data.Manifold.PseudoAffine
import Data.Complex
import Data.List
import Data.AffineSpace
import Data.VectorSpace
import Math.LinearMap.Category
import qualified Control.Functor.Constrained as CC
import qualified Control.Arrow.Constrained as CC
import qualified Control.Applicative.Constrained as CC

import Data.Functor
import Control.Monad
import Control.Applicative
import Data.Tagged
import Data.Type.Coercion
import GHC.Generics
import Control.Lens (Prism', prism', view, re, (^.))

import qualified Test.QuickCheck as QC


-- | Piecewise-constant function with regular, power-of-two subdivisions, but
--   not necessarily with homogeneous resolution. 
--   The name refers to the fact that this type effectively contains a decomposition
--   in a basis of Haar wavelets.
type family Haar x y

class HaarSamplingDomain x where
  evalHaarFunction :: VAffineSpace y
            => Haar x y -> x -> y
  homsampleHaarFunction :: (VAffineSpace y, Diff y ~ y, Fractional (Scalar y))
            => PowerOfTwo -> (x -> y) -> Haar x y
  dirac :: x -> DualVector (Haar x ℝ)

-- | Piecewise-constant functions on the unit interval whose integral is zero.
data Haar0BiasTree (dn :: Dualness) (y :: *)
  = HaarZero
  | HaarUnbiased
     { haarUnbiasedOffsAmpl :: !y
         -- ^ Offset-amplitude between the left and right half
     , haarUnbiasedLHFFluct :: (Haar0BiasTree dn y)
         -- ^ Left half of the function domain, \([-1\ldots 0[\)
     , haarUnbiasedRHFFluct :: (Haar0BiasTree dn y)
         -- ^ Right half, i.e. \([0\ldots 1]\).
     }
 deriving (Show)

type HaarUnbiased y = Haar0BiasTree FunctionSpace y

data Haar_D¹ dn y = Haar_D¹
    { pwconst_D¹_offset :: !y
    , pwconst_D¹_variation :: Haar0BiasTree dn y }
deriving instance (Show y, Show (Diff y)) => Show (Haar_D¹ dn y)

newtype Haar_S¹ (dn :: Dualness) (y :: *)
    = Haar_S¹ { getUnclosedHaarS¹Function :: Haar_D¹ dn y }
deriving instance (Show y, Show (Diff y)) => Show (Haar_S¹ dn y)

type instance Haar D¹ y = Haar_D¹ FunctionSpace y
type instance Haar S¹ y = Haar_S¹ FunctionSpace y

instance Num' s
   => CC.Functor (Haar0BiasTree dn) (LinearFunction s) (LinearFunction s) where
  fmap f = LinearFunction go
   where go HaarZero = HaarZero
         go (HaarUnbiased δ l r) = HaarUnbiased (f CC.$ δ) (go l) (go r)

instance ∀ s dn . Num' s
    => CC.Functor (Haar_D¹ dn) (LinearFunction s) (LinearFunction s) where
  fmap = fmapLFH
   where fmapLFH :: ∀ y z . ( TensorSpace y, TensorSpace z, Scalar y ~ s, Scalar z ~ s )
             => (y-+>z) -> (Haar_D¹ dn y-+>Haar_D¹ dn z)
         fmapLFH f = case (linearManifoldWitness @z, linearManifoldWitness @y) of
          (LinearManifoldWitness _, LinearManifoldWitness _) ->
           LinearFunction $
            \(Haar_D¹ y₀ δs) -> Haar_D¹ (f CC.$ y₀)
                      $ getLinearFunction (CC.fmap f) δs

instance ∀ s dn . Num' s
    => CC.Functor (Haar_S¹ dn) (LinearFunction s) (LinearFunction s) where
  fmap = fmapLFH
   where fmapLFH :: ∀ y z . ( TensorSpace y, TensorSpace z, Scalar y ~ s, Scalar z ~ s )
             => (y-+>z) -> (Haar_S¹ dn y-+>Haar_S¹ dn z)
         fmapLFH f = case (linearManifoldWitness @z, linearManifoldWitness @y) of
          (LinearManifoldWitness _, LinearManifoldWitness _) ->
           LinearFunction $ \(Haar_S¹ g)
             -> Haar_S¹ . getLinearFunction (CC.fmap f) $ g

instance ∀ s dn . Num' s
     => CC.Monoidal (Haar0BiasTree dn) (LinearFunction s) (LinearFunction s) where
  pureUnit = LinearFunction $ \Origin -> HaarZero
  fzipWith = fzwLFH
   where fzwLFH :: ∀ a b c .
                   ( TensorSpace a, TensorSpace b, TensorSpace c
                   , Scalar a ~ s, Scalar b ~ s, Scalar c ~ s )
              => ((a,b)-+>c)
               -> ((Haar0BiasTree dn a, Haar0BiasTree dn b) -+> Haar0BiasTree dn c)
         fzwLFH = case ( linearManifoldWitness @a
                       , linearManifoldWitness @b
                       , linearManifoldWitness @c ) of
          (LinearManifoldWitness _, LinearManifoldWitness _, LinearManifoldWitness _)
           -> \f ->
            let go (HaarZero, y) = getLinearFunction
                 (CC.fmap (f CC.. LinearFunction (zeroV,))) $ y
                go (x, HaarZero) = getLinearFunction
                 (CC.fmap (f CC.. LinearFunction (,zeroV))) $ x
                go (HaarUnbiased δx lx rx, HaarUnbiased δy ly ry)
                 = HaarUnbiased (f CC.$ (δx,δy)) (go (lx,ly)) (go (rx,ry))
            in LinearFunction go

instance ∀ s dn . Num' s
    => CC.Monoidal (Haar_D¹ dn) (LinearFunction s) (LinearFunction s) where
  pureUnit = LinearFunction $ \Origin -> zeroV
  fzipWith = fzwLFH
   where fzwLFH :: ∀ x y z dn . 
                      ( TensorSpace x, TensorSpace y, TensorSpace z
                      , Scalar x ~ s, Scalar y ~ s, Scalar z ~ s )
                   => ((x,y)-+>z) -> ((Haar_D¹ dn x, Haar_D¹ dn y) -+> Haar_D¹ dn z)
         fzwLFH = case ( linearManifoldWitness @x
                       , linearManifoldWitness @y
                       , linearManifoldWitness @z ) of
          (LinearManifoldWitness _, LinearManifoldWitness _, LinearManifoldWitness _)
             -> \f -> LinearFunction
                   $ \(Haar_D¹ x δxs, Haar_D¹ y δys)
                        -> Haar_D¹ (f CC.$ (x,y))
                                   (getLinearFunction (CC.fzipWith f) (δxs,δys))

instance ∀ s dn . Num' s
    => CC.Monoidal (Haar_S¹ dn) (LinearFunction s) (LinearFunction s) where
  pureUnit = LinearFunction $ \Origin -> zeroV
  fzipWith = fzwLFH
   where fzwLFH :: ∀ x y z dn . 
                      ( TensorSpace x, TensorSpace y, TensorSpace z
                      , Scalar x ~ s, Scalar y ~ s, Scalar z ~ s )
                   => ((x,y)-+>z) -> ((Haar_S¹ dn x, Haar_S¹ dn y) -+> Haar_S¹ dn z)
         fzwLFH = case ( linearManifoldWitness @x
                       , linearManifoldWitness @y
                       , linearManifoldWitness @z ) of
          (LinearManifoldWitness _, LinearManifoldWitness _, LinearManifoldWitness _)
             -> \f -> LinearFunction
                   $ \(Haar_S¹ xs, Haar_S¹ ys)
                        -> Haar_S¹ (getLinearFunction (CC.fzipWith f) (xs,ys))
         
evalHaar_D¹ :: VAffineSpace y => Haar D¹ y -> D¹ -> y
evalHaar_D¹ (Haar_D¹ offs varis) x = offs .+^ evalVari varis x
 where evalVari HaarZero _ = zeroV
       evalVari (HaarUnbiased δlr lh rh) p = case p^.halves of
        Left pl  -> evalVari lh pl ^-^ δlr
        Right pr -> evalVari rh pr ^+^ δlr

evalHaar_S¹ :: VAffineSpace y => Haar S¹ y -> S¹ -> y
evalHaar_S¹ (Haar_S¹ f) (S¹Polar ϑ) = evalHaar_D¹ f (D¹ $ ϑ/pi)

homsampleHaar_D¹ :: (VAffineSpace y, Diff y ~ y, Fractional (Scalar y))
            => PowerOfTwo -> (D¹ -> y) -> Haar D¹ y
homsampleHaar_D¹ (TwoToThe i) _ | i<0  = error "Cannot sample function at resolution <0."
homsampleHaar_D¹ (TwoToThe 0) f = Haar_D¹ (f $ D¹ 0) HaarZero
homsampleHaar_D¹ (TwoToThe i) f
   = case homsampleHaar_D¹ (TwoToThe $ i-1) <$> [ f . view (re leftHalf)
                                                , f . view (re rightHalf) ] of
       [Haar_D¹ y₀l sfl, Haar_D¹ y₀r sfr]
        -> Haar_D¹ ((y₀l^+^y₀r)^/2) $ HaarUnbiased ((y₀r^-^y₀l)^/2) sfl sfr

homsampleHaar_S¹ :: (VAffineSpace y, Diff y ~ y, Fractional (Scalar y))
            => PowerOfTwo -> (S¹ -> y) -> Haar S¹ y
homsampleHaar_S¹ r f = Haar_S¹ . homsampleHaar_D¹ r $ f . \(D¹ x) -> S¹Polar $ x*pi

boxDistributionD¹ :: (VectorSpace y, RealFrac (Scalar y))
                     => (D¹, D¹) -> y -> Haar_D¹ DistributionSpace y
boxDistributionD¹ (D¹ l, D¹ r) y
  | l > r      = boxDistributionD¹ (D¹ r, D¹ l) y
boxDistributionD¹ (D¹ (-1), D¹ 1) y
               = Haar_D¹ y zeroV
boxDistributionD¹ (D¹ l, D¹ r) y
  | l<0, r>0   = Haar_D¹ y $ HaarUnbiased (wr^-^wl)    lstru rstru
  | l<0        = Haar_D¹ y $ HaarUnbiased (negateV wl) lstru zeroV
  | otherwise  = Haar_D¹ y $ HaarUnbiased wr           zeroV rstru
 where Haar_D¹ wl lstru = boxDistributionD¹ (D¹ $ l*2 + 1, D¹ $ min 0 r*2 + 1)
                            $ y^*if r>0 then realToFrac $ l/(l-r) else 1
       Haar_D¹ wr rstru = boxDistributionD¹ (D¹ $ max 0 l*2 - 1, D¹ $ r*2 - 1)
                            $ y^*if l<0 then realToFrac $ r/(r-l) else 1

boxDistributionS¹ :: (VectorSpace y, Scalar y ~ Double, AffineSpace y, y ~ Diff y)
                     => (S¹, S¹) -> y -> Haar_S¹ DistributionSpace y
boxDistributionS¹ (S¹Polar ϑl, S¹Polar ϑr) y
  | ϑl > ϑr    = Haar_S¹ $ boxDistributionD¹ (D¹ l, D¹ 1) (y^*(ll/li))
                         ^+^ boxDistributionD¹ (D¹ $ -1, D¹ r) (y^*(lr/li))
  | otherwise  = Haar_S¹ $ boxDistributionD¹ (D¹ l, D¹ r) y
 where l = ϑl/pi; r = ϑr/pi
       ll = 1-l; lr = r+1
       li = ll + lr

diracD¹ :: D¹ -> DualVector (Haar D¹ ℝ)
diracD¹ x₀ = boxDistributionD¹ (x₀,x₀) 1

diracS¹ :: S¹ -> DualVector (Haar S¹ ℝ)
diracS¹ x₀ = boxDistributionS¹ (x₀,x₀) 1


-- | Given a function \(f\) and an interval \((\ell,r)\), yield the integral
--   \(\backslash x \mapsto \int\limits_{\ell}^r \mathrm{d}t\: f(t)\).
integrateHaarFunction :: (VectorSpace y, RealFrac (Scalar y)) => Haar D¹ y -> (D¹,D¹) -> y
integrateHaarFunction f = \(l,r) -> antideriv f r ^+^ c l
 where c (D¹ 0) = case f of Haar_D¹ _ (HaarUnbiased yr _ _) -> yr
                            _                               -> zeroV
       c l = negateV $ antideriv f l
       antideriv (Haar_D¹ y₀ ff) p@(D¹ x) = realToFrac x*^y₀ ^+^ down ff p^/2
       down HaarZero _ = zeroV
       down (HaarUnbiased δlr fl fr) p = ( case p^.halves of
        Left pl  -> antideriv (Haar_D¹ (negateV δlr) fl) pl
        Right pr -> antideriv (Haar_D¹          δlr  fr) pr ) ^-^ δlr


instance HaarSamplingDomain D¹ where
  evalHaarFunction = evalHaar_D¹
  homsampleHaarFunction = homsampleHaar_D¹
  dirac = diracD¹

instance HaarSamplingDomain S¹ where
  evalHaarFunction = evalHaar_S¹
  homsampleHaarFunction = homsampleHaar_S¹
  dirac = diracS¹


instance QC.Arbitrary PowerOfTwo where
  arbitrary = do
    QC.Positive i <- QC.arbitrary
    return . TwoToThe . ceiling . logBase 2 $ fromInteger i
  shrink (TwoToThe i) = TwoToThe <$> [0 .. i-1]

instance AdditiveGroup y => AffineSpace (Haar0BiasTree dn y) where
  type Diff (Haar0BiasTree dn y) = Haar0BiasTree dn y
  HaarZero .+^ f = f
  f .+^ HaarZero = f
  HaarUnbiased δlr₀ δsl₀ δsr₀ .+^ HaarUnbiased δlr₁ δsl₁ δsr₁
            = HaarUnbiased (δlr₀^+^δlr₁) (δsl₀.+^δsl₁) (δsr₀.+^δsr₁)
  HaarZero .-. HaarZero = HaarZero
  f .-. HaarZero = f
  HaarZero .-. f = negateV f
  HaarUnbiased δlr₀ δsl₀ δsr₀ .-. HaarUnbiased δlr₁ δsl₁ δsr₁
            = HaarUnbiased (δlr₀^-^δlr₁) (δsl₀.-.δsl₁) (δsr₀.-.δsr₁)

instance AdditiveGroup y => AdditiveGroup (Haar0BiasTree dn y) where
  (^+^) = (.+^)
  (^-^) = (.-.)
  zeroV = HaarZero
  negateV HaarZero = HaarZero
  negateV (HaarUnbiased δlr δsl δsr) = HaarUnbiased (negateV δlr) (negateV δsl) (negateV δsr)

instance VectorSpace y => VectorSpace (Haar0BiasTree dn y) where
  type Scalar (Haar0BiasTree dn y) = Scalar y
  _ *^ HaarZero = HaarZero
  μ *^ HaarUnbiased δlr δsl δsr = HaarUnbiased (μ*^δlr) (μ*^δsl) (μ*^δsr)
  
instance VAffineSpace y => AffineSpace (Haar_D¹ dn y) where
  type Diff (Haar_D¹ dn y) = Haar_D¹ dn (Diff y)
  Haar_D¹ y₀ δ₀ .+^ Haar_D¹ y₁ δ₁ = Haar_D¹ (y₀.+^y₁) (δ₀.+^δ₁)
  Haar_D¹ y₀ δ₀ .-. Haar_D¹ y₁ δ₁ = Haar_D¹ (y₀.-.y₁) (δ₀.-.δ₁)

instance VAffineSpace y => AffineSpace (Haar_S¹ dn y) where
  type Diff (Haar_S¹ dn y) = Haar_S¹ dn (Diff y)
  Haar_S¹ f₀ .+^ Haar_S¹ f₁ = Haar_S¹ $ f₀ .+^ f₁
  Haar_S¹ f₀ .-. Haar_S¹ f₁ = Haar_S¹ $ f₀ .-. f₁

instance VAffineSpace y
             => AdditiveGroup (Haar_D¹ dn y) where
  zeroV = Haar_D¹ zeroV zeroV
  (^+^) = (.+^)
  (^-^) = (.-.)
  negateV (Haar_D¹ y δ) = Haar_D¹ (negateV y) (negateV δ)

instance VAffineSpace y
             => AdditiveGroup (Haar_S¹ dn y) where
  zeroV = Haar_S¹ zeroV
  (^+^) = (.+^)
  (^-^) = (.-.)
  negateV (Haar_S¹ f) = Haar_S¹ $ negateV f

instance VAffineSpace y
             => VectorSpace (Haar_D¹ dn y) where
  type Scalar (Haar_D¹ dn y) = Scalar y
  μ *^ Haar_D¹ y δ = Haar_D¹ (μ*^y) (μ*^δ)

instance VAffineSpace y
             => VectorSpace (Haar_S¹ dn y) where
  type Scalar (Haar_S¹ dn y) = Scalar y
  μ *^ Haar_S¹ f = Haar_S¹ $ μ*^f

instance (InnerSpace y, Fractional (Scalar y)) => InnerSpace (HaarUnbiased y) where
  HaarZero <.> _ = 0
  _ <.> HaarZero = 0
  HaarUnbiased δlr₀ δsl₀ δsr₀ <.> HaarUnbiased δlr₁ δsl₁ δsr₁
            = δlr₀<.>δlr₁ + (δsl₀<.>δsl₁)/2 + (δsr₀<.>δsr₁)/2

-- | 𝓛² product on [-1…1] functions, i.e. @𝑓<.>𝑔 ⩵ ₋₁∫¹ d𝑥 𝑓(𝑥)·𝑔(𝑥)@
instance (InnerSpace y, Fractional (Scalar y), AffineSpace y, Diff y ~ y)
             => InnerSpace (Haar_D¹ FunctionSpace y) where
  Haar_D¹ y₀ δ₀ <.> Haar_D¹ y₁ δ₁ = 2*(y₀<.>y₁ + δ₀<.>δ₁)

-- | 𝓛² product on 𝑆¹ functions, i.e. @𝑓<.>𝑔 ⩵ ∫_𝑆¹ dϑ 𝑓(ϑ)·𝑔(ϑ)@
instance (InnerSpace y, Floating (Scalar y), AffineSpace y, Diff y ~ y)
             => InnerSpace (Haar_S¹ FunctionSpace y) where
  Haar_S¹ f₀ <.> Haar_S¹ f₁ = pi*(f₀<.>f₁)

instance VAffineSpace y
             => Semimanifold (Haar0BiasTree dn y) where
  type Needle (Haar0BiasTree dn y) = Haar0BiasTree dn y
  type Interior (Haar0BiasTree dn y) = Haar0BiasTree dn y
  translateP = Tagged (.+^)
  toInterior = Just
  fromInterior = id
instance VAffineSpace y
             => PseudoAffine (Haar0BiasTree dn y) where
  (.-~!) = (.-.)

instance VAffineSpace y
             => Semimanifold (Haar_D¹ dn y) where
  type Needle (Haar_D¹ dn y) = Haar_D¹ dn y
  type Interior (Haar_D¹ dn y) = Haar_D¹ dn y
  translateP = Tagged (.+^)
  toInterior = Just
  fromInterior = id
instance ( VAffineSpace y )
             => PseudoAffine (Haar_D¹ dn y) where
  (.-~!) = (.-.)

instance VAffineSpace y
             => Semimanifold (Haar_S¹ dn y) where
  type Needle (Haar_S¹ dn y) = Haar_S¹ dn y
  type Interior (Haar_S¹ dn y) = Haar_S¹ dn y
  translateP = Tagged (.+^)
  toInterior = Just
  fromInterior = id
instance ( VAffineSpace y )
             => PseudoAffine (Haar_S¹ dn y) where
  (.-~!) = (.-.)

instance ∀ y dn . ( TensorSpace y, VAffineSpace y, Num' (Scalar y) )
             => TensorSpace (Haar0BiasTree dn y) where
  type TensorProduct (Haar0BiasTree dn y) w = Haar0BiasTree dn (y⊗w)
  wellDefinedVector HaarZero = Just HaarZero
  wellDefinedVector (HaarUnbiased δ l r) = HaarUnbiased <$> wellDefinedVector δ
                                          <*> wellDefinedVector l
                                          <*> wellDefinedVector r
  wellDefinedTensor (Tensor HaarZero) = Just $ Tensor HaarZero
  wellDefinedTensor (Tensor (HaarUnbiased δ l r)) = Tensor <$>
                                   (HaarUnbiased <$> wellDefinedVector δ
                                          <*> wellDefinedVector l
                                          <*> wellDefinedVector r)
  scalarSpaceWitness = case scalarSpaceWitness :: ScalarSpaceWitness y of
     ScalarSpaceWitness -> ScalarSpaceWitness
  linearManifoldWitness = case linearManifoldWitness :: LinearManifoldWitness y of
     LinearManifoldWitness BoundarylessWitness -> LinearManifoldWitness BoundarylessWitness
  coerceFmapTensorProduct = cftlp
   where cftlp :: ∀ a b p . p (Haar0BiasTree dn y) -> Coercion a b
                   -> Coercion (Haar0BiasTree dn (Diff y⊗a))
                               (Haar0BiasTree dn (Diff y⊗b))
         cftlp _ c = case CC.fmap c :: Coercion (y⊗a) (y⊗b) of
            Coercion -> Coercion
  zeroTensor = Tensor zeroV
  toFlatTensor = case scalarSpaceWitness @y of
    ScalarSpaceWitness -> LinearFunction Tensor CC.. CC.fmap toFlatTensor
  fromFlatTensor = case scalarSpaceWitness @y of
    ScalarSpaceWitness -> CC.fmap fromFlatTensor CC.. LinearFunction getTensorProduct
  addTensors (Tensor f) (Tensor g) = Tensor $ f^+^g
  scaleTensor = bilinearFunction $ \μ (Tensor f) -> Tensor $ μ*^f
  negateTensor = LinearFunction $ \(Tensor f) -> Tensor $ negateV f
  tensorProduct = case scalarSpaceWitness @y of
    ScalarSpaceWitness -> bilinearFunction
         $ \f w -> Tensor $ CC.fmap (LinearFunction $ \y -> y⊗w) CC.$ f
  transposeTensor = case scalarSpaceWitness @y of
   ScalarSpaceWitness -> LinearFunction $
    \case (Tensor HaarZero) -> zeroV
          (Tensor (HaarUnbiased δyw δsl δsr))
           -> (CC.fmap (LinearFunction $ \δy -> HaarUnbiased δy zeroV zeroV)
                 CC.. transposeTensor CC.$ δyw)
             ^+^ (CC.fmap (LinearFunction $ \δysl -> HaarUnbiased zeroV δysl zeroV)
                 CC.. transposeTensor CC.$ Tensor δsl)
             ^+^ (CC.fmap (LinearFunction $ \δysr -> HaarUnbiased zeroV zeroV δysr)
                 CC.. transposeTensor CC.$ Tensor δsr)
  fmapTensor = case scalarSpaceWitness @y of
   ScalarSpaceWitness -> bilinearFunction $ \a (Tensor f)
             -> Tensor $ CC.fmap (CC.fmap a) CC.$ f
  fzipTensorWith = case scalarSpaceWitness @y of
   ScalarSpaceWitness -> bilinearFunction $ \a (Tensor f, Tensor g)
             -> Tensor $ CC.fzipWith (getLinearFunction fzipTensorWith a) CC.$ (f,g)
instance ∀ y dn
         . (TensorSpace y, VAffineSpace y, Num' (Scalar y))
             => TensorSpace (Haar_D¹ dn y) where
  type TensorProduct (Haar_D¹ dn y) w = Haar_D¹ dn (y⊗w)
  wellDefinedVector = case scalarSpaceWitness @y of
   ScalarSpaceWitness -> \(Haar_D¹ y₀ δs)
       -> Haar_D¹ <$> wellDefinedVector y₀ <*> wellDefinedVector δs
  wellDefinedTensor = case scalarSpaceWitness @y of
   ScalarSpaceWitness -> \(Tensor (Haar_D¹ y₀ δs))
       -> Tensor <$> (Haar_D¹ <$> wellDefinedVector y₀ <*> wellDefinedVector δs)
  scalarSpaceWitness = case scalarSpaceWitness :: ScalarSpaceWitness y of
     ScalarSpaceWitness -> ScalarSpaceWitness
  linearManifoldWitness = case linearManifoldWitness :: LinearManifoldWitness y of
     LinearManifoldWitness BoundarylessWitness -> LinearManifoldWitness BoundarylessWitness
  coerceFmapTensorProduct = cftlp
   where cftlp :: ∀ a b p . p (Haar_D¹ dn y) -> Coercion a b
                   -> Coercion (Haar_D¹ dn (Diff y ⊗ a))
                               (Haar_D¹ dn (Diff y ⊗ b))
         cftlp _ c = case CC.fmap c :: Coercion (y ⊗ a) (y ⊗ b) of
            Coercion -> Coercion
  zeroTensor = Tensor zeroV
  toFlatTensor = case scalarSpaceWitness @y of
   ScalarSpaceWitness -> LinearFunction Tensor CC.. CC.fmap toFlatTensor
  fromFlatTensor = case scalarSpaceWitness @y of
   ScalarSpaceWitness -> CC.fmap fromFlatTensor CC.. LinearFunction getTensorProduct
  addTensors (Tensor f) (Tensor g) = Tensor $ f^+^g
  scaleTensor = bilinearFunction $ \μ (Tensor f) -> Tensor $ μ*^f
  negateTensor = LinearFunction $ \(Tensor f) -> Tensor $ negateV f
  tensorProduct = case scalarSpaceWitness @y of
   ScalarSpaceWitness -> bilinearFunction
         $ \f w -> Tensor $ CC.fmap (LinearFunction $ \y -> y⊗w) CC.$ f
  transposeTensor = case scalarSpaceWitness @y of
   ScalarSpaceWitness -> LinearFunction $
       \(Tensor (Haar_D¹ yw₀ δs))
           -> (CC.fmap (LinearFunction $ (`Haar_D¹`zeroV)) CC.. transposeTensor CC.$ yw₀)
             ^+^ (CC.fmap (LinearFunction $ Haar_D¹ zeroV)
                   CC.. transposeTensor CC.$ Tensor δs)
  fmapTensor = case scalarSpaceWitness @y of
   ScalarSpaceWitness -> bilinearFunction $ \a (Tensor f)
             -> Tensor $ CC.fmap (CC.fmap a) CC.$ f
  fzipTensorWith = case scalarSpaceWitness @y of
   ScalarSpaceWitness -> bilinearFunction $ \a (Tensor f, Tensor g)
             -> Tensor $ CC.fzipWith (getLinearFunction fzipTensorWith a) CC.$ (f,g)

instance ∀ y dn
         . (TensorSpace y, VAffineSpace y, Num' (Scalar y))
             => TensorSpace (Haar_S¹ dn y) where
  type TensorProduct (Haar_S¹ dn y) w = Haar_S¹ dn (y⊗w)
  wellDefinedVector = case scalarSpaceWitness @y of
   ScalarSpaceWitness -> \(Haar_S¹ f)
       -> Haar_S¹ <$> wellDefinedVector f
  wellDefinedTensor = case scalarSpaceWitness @y of
   ScalarSpaceWitness -> \(Tensor (Haar_S¹ f))
       -> Tensor <$> (Haar_S¹ <$> wellDefinedVector f)
  scalarSpaceWitness = case scalarSpaceWitness :: ScalarSpaceWitness y of
     ScalarSpaceWitness -> ScalarSpaceWitness
  linearManifoldWitness = case linearManifoldWitness :: LinearManifoldWitness y of
     LinearManifoldWitness BoundarylessWitness -> LinearManifoldWitness BoundarylessWitness
  coerceFmapTensorProduct = cftlp
   where cftlp :: ∀ a b p . p (Haar_S¹ dn y) -> Coercion a b
                   -> Coercion (Haar_S¹ dn (Diff y ⊗ a))
                               (Haar_S¹ dn (Diff y ⊗ b))
         cftlp _ c = case CC.fmap c :: Coercion (y ⊗ a) (y ⊗ b) of
            Coercion -> Coercion
  zeroTensor = Tensor zeroV
  toFlatTensor = case scalarSpaceWitness @y of
   ScalarSpaceWitness -> LinearFunction Tensor CC.. CC.fmap toFlatTensor
  fromFlatTensor = case scalarSpaceWitness @y of
   ScalarSpaceWitness -> CC.fmap fromFlatTensor CC.. LinearFunction getTensorProduct
  addTensors (Tensor f) (Tensor g) = Tensor $ f^+^g
  scaleTensor = bilinearFunction $ \μ (Tensor f) -> Tensor $ μ*^f
  negateTensor = LinearFunction $ \(Tensor f) -> Tensor $ negateV f
  tensorProduct = case scalarSpaceWitness @y of
   ScalarSpaceWitness -> bilinearFunction
         $ \f w -> Tensor $ CC.fmap (LinearFunction $ \y -> y⊗w) CC.$ f
  transposeTensor = case scalarSpaceWitness @y of
   ScalarSpaceWitness -> LinearFunction $
       \(Tensor (Haar_S¹ fw))
           -> CC.fmap (LinearFunction Haar_S¹) CC.. transposeTensor CC.$ Tensor fw
  fmapTensor = case scalarSpaceWitness @y of
   ScalarSpaceWitness -> bilinearFunction $ \a (Tensor f)
             -> Tensor $ CC.fmap (CC.fmap a) CC.$ f
  fzipTensorWith = case scalarSpaceWitness @y of
   ScalarSpaceWitness -> bilinearFunction $ \a (Tensor f, Tensor g)
             -> Tensor $ CC.fzipWith (getLinearFunction fzipTensorWith a) CC.$ (f,g)



instance ∀ y dn
         . ( LinearSpace y, VAffineSpace y, Num' (Scalar y), ValidDualness dn
           , AffineSpace (DualVector y), Diff (DualVector y) ~ DualVector y )
             => LinearSpace (Haar0BiasTree dn y) where
  type DualVector (Haar0BiasTree dn y) = Haar0BiasTree (Dual dn) (DualVector y)
  dualSpaceWitness = case ( dualSpaceWitness :: DualSpaceWitness y
                          , dualityWitness :: DualityWitness dn ) of
       (DualSpaceWitness, DualityWitness) -> DualSpaceWitness
  linearId = LinearMap hId
   where hId = case dualSpaceWitness :: DualSpaceWitness y of
          DualSpaceWitness
            -> HaarUnbiased (case linearId :: y+>y of
                        LinearMap yId
                            -> CC.fmap (LinearFunction
                                             $ \y -> HaarUnbiased y zeroV zeroV)
                                         CC.$ (Tensor yId :: DualVector y⊗y))
                     (CC.fmap (CC.fmap . LinearFunction
                                        $ \l -> HaarUnbiased zeroV l zeroV) CC.$ hId)
                     (CC.fmap (CC.fmap  . LinearFunction
                                        $ \r -> HaarUnbiased zeroV zeroV r) CC.$ hId)
  tensorId = LinearMap $ hId
   where hId :: ∀ w . (LinearSpace w, Scalar w ~ Scalar y)
               => Haar0BiasTree (Dual dn)
                    (Tensor (Scalar (DualVector y))
                            (DualVector y)
                            (Tensor (Scalar y) (DualVector w) (Haar0BiasTree dn y ⊗ w)))
         hId = case ( dualSpaceWitness :: DualSpaceWitness y
                    , dualSpaceWitness :: DualSpaceWitness w ) of
          (DualSpaceWitness, DualSpaceWitness)
            -> HaarUnbiased (case tensorId :: (y⊗w)+>(y⊗w) of
                        LinearMap ywId
                            -> CC.fmap (CC.fmap $ LinearFunction
                                          $ \yw -> Tensor $ HaarUnbiased yw zeroV zeroV)
                                       CC.$ (Tensor ywId
                                              :: DualVector y⊗(DualVector w⊗(y⊗w))))
                     (CC.fmap (CC.fmap . CC.fmap . LinearFunction
                            $ \(Tensor l) -> Tensor $ HaarUnbiased zeroV l zeroV) CC.$ hId)
                     (CC.fmap (CC.fmap . CC.fmap . LinearFunction
                            $ \(Tensor r) -> Tensor $ HaarUnbiased zeroV zeroV r) CC.$ hId)
  applyDualVector = bilinearFunction $ \a f -> go a f
   where go :: Haar0BiasTree (Dual dn) (DualVector y) -> Haar0BiasTree dn y -> Scalar y
         go HaarZero _ = zeroV
         go _ HaarZero = zeroV
         go (HaarUnbiased δa al ar) (HaarUnbiased δy fl fr)
          = case (dualSpaceWitness @y, scalarSpaceWitness @y) of
           (DualSpaceWitness, ScalarSpaceWitness)
               -> (getLinearFunction applyDualVector δa CC.$ δy) + go al fl + go ar fr
  applyTensorFunctional = bilinearFunction $ \(LinearMap a) (Tensor f)
                        -> go a f
   where go :: ∀ u . (LinearSpace u, Scalar u ~ Scalar y)
             => Haar0BiasTree (Dual dn) (DualVector y⊗DualVector u)
                   -> Haar0BiasTree dn (y⊗u) -> Scalar y
         go HaarZero _ = zeroV
         go _ HaarZero = zeroV
         go (HaarUnbiased (Tensor δa) al ar) (HaarUnbiased δy fl fr)
          = case (dualSpaceWitness @y, scalarSpaceWitness @y) of
           (DualSpaceWitness, ScalarSpaceWitness)
               -> (getLinearFunction applyDualVector (LinearMap δa :: y+>DualVector u) CC.$ δy)
                    + go al fl + go ar fr
  applyLinear = bilinearFunction $ \(LinearMap a) f -> go a f
   where go :: ∀ w . (TensorSpace w, Scalar w ~ Scalar y)
                => Haar0BiasTree (Dual dn) (Tensor (Scalar (DualVector y)) (DualVector y) w)
                      -> Haar0BiasTree dn y -> w
         go HaarZero _ = zeroV
         go _ HaarZero = zeroV
         go (HaarUnbiased (Tensor δa) al ar) (HaarUnbiased δy fl fr)
               = ( (getLinearFunction applyLinear (LinearMap δa :: y+>w)) CC.$ δy )
                   ^+^ go al fl ^+^ go ar fr
  applyTensorLinMap = bilinearFunction $ \(LinearMap a) (Tensor f)
                 -> go a f
   where go :: ∀ u w . ( LinearSpace u, Scalar u ~ Scalar y
                       , TensorSpace w, Scalar w ~ Scalar y )
                => Haar0BiasTree (Dual dn) (Tensor
                           (Scalar (DualVector y))
                            (DualVector y)
                            (Tensor (Scalar y) (DualVector u) w))
                 -> Haar0BiasTree dn (y⊗u) -> w
         go HaarZero _ = zeroV
         go _ HaarZero = zeroV
         go (HaarUnbiased (Tensor δa) al ar) (HaarUnbiased δyu fl fr)
               = ( (getLinearFunction applyTensorLinMap
                          (LinearMap δa :: (y⊗u)+>w)) CC.$ δyu )
                   ^+^ go al fl ^+^ go ar fr
                 
instance ∀ y dn .
           ( LinearSpace y, VAffineSpace y, Num' (Scalar y), ValidDualness dn
           , AffineSpace (DualVector y), Diff (DualVector y) ~ DualVector y ) 
             => LinearSpace (Haar_D¹ dn y) where
  type DualVector (Haar_D¹ dn y) = Haar_D¹ (Dual dn) (DualVector y)
  dualSpaceWitness = case ( dualSpaceWitness :: DualSpaceWitness y
                          , dualityWitness :: DualityWitness dn ) of
       (DualSpaceWitness, DualityWitness) -> DualSpaceWitness
  linearId = LinearMap hId
   where hId = case dualSpaceWitness :: DualSpaceWitness y of
          DualSpaceWitness
            -> Haar_D¹ (case linearId :: y+>y of
                        LinearMap yId
                            -> CC.fmap (LinearFunction
                                             $ \y -> Haar_D¹ y zeroV)
                                         CC.$ (Tensor yId :: DualVector y⊗y))
                       (CC.fmap (CC.fmap . LinearFunction
                                          $ \δs -> Haar_D¹ zeroV δs) CC.$ getLinearMap
                                              (linearId :: Haar0BiasTree dn y+>Haar0BiasTree dn y))
  tensorId = LinearMap $ hId
   where hId :: ∀ w . (LinearSpace w, Scalar w ~ Scalar y)
               => Haar_D¹ (Dual dn)
                    (Tensor (Scalar (DualVector y))
                            (DualVector y)
                            (Tensor (Scalar y) (DualVector w)
                                (Tensor (Scalar y) (Haar_D¹ dn y) w)))
         hId = case ( dualSpaceWitness :: DualSpaceWitness y
                    , dualSpaceWitness :: DualSpaceWitness w ) of
          (DualSpaceWitness, DualSpaceWitness)
            -> Haar_D¹ (case tensorId :: (y⊗w)+>(y⊗w) of
                        LinearMap ywId
                            -> CC.fmap (CC.fmap $ LinearFunction
                                          $ \yw -> Tensor $ Haar_D¹ yw zeroV)
                                       CC.$ (undefined -- Tensor ywId
                                              :: DualVector y⊗(DualVector w⊗(y⊗w))))
                       (case tensorId :: (Haar0BiasTree dn y⊗w)+>(Haar0BiasTree dn y⊗w) of
                          LinearMap h₀ywId
                           -> CC.fmap (CC.fmap . CC.fmap . LinearFunction
                                       $ \(Tensor q) -> Tensor (Haar_D¹ zeroV q))
                                 CC.$ h₀ywId)
  applyDualVector = bilinearFunction $ \(Haar_D¹ a₀ δa) (Haar_D¹ f₀ δf)
      -> case (dualSpaceWitness @y, scalarSpaceWitness @y) of
           (DualSpaceWitness, ScalarSpaceWitness)
                -> (getLinearFunction applyDualVector a₀ CC.$ f₀)
                 + (getLinearFunction applyDualVector δa CC.$ δf)
  applyTensorFunctional = bilinearFunction $ \(LinearMap a) (Tensor f) -> go a f
   where go :: ∀ u . (LinearSpace u, Scalar u ~ Scalar y)
             => Haar_D¹ (Dual dn) (DualVector y⊗DualVector u)
                 -> Haar_D¹ dn (y⊗u) -> Scalar y
         go (Haar_D¹ (Tensor a₀) δa) (Haar_D¹ f₀ δf)
          = case ( dualSpaceWitness @y, dualSpaceWitness @u, scalarSpaceWitness @y ) of
           (DualSpaceWitness, DualSpaceWitness, ScalarSpaceWitness)
               -> (getLinearFunction applyDualVector (LinearMap a₀ :: y+>DualVector u)
                                                              CC.$ f₀)
                + (getLinearFunction applyDualVector
                              (Coercion CC.$ δa) CC.$ δf)
  applyLinear = bilinearFunction $ \(LinearMap a) f -> go a f
   where go :: ∀ w . (TensorSpace w, Scalar w ~ Scalar y)
                => Haar_D¹ (Dual dn) (Tensor (Scalar (DualVector y)) (DualVector y) w)
                      -> Haar_D¹ dn y -> w
         go (Haar_D¹ (Tensor a₀) δa) (Haar_D¹ f₀ δf)
           = ( (getLinearFunction applyLinear (LinearMap a₀ :: y+>w)) CC.$ f₀ )
          ^+^ ( getLinearFunction applyLinear (LinearMap δa :: Haar0BiasTree dn y+>w) CC.$ δf )
  applyTensorLinMap = bilinearFunction $ \(LinearMap a) (Tensor f) -> go a f
   where go :: ∀ u w . ( LinearSpace u, Scalar u ~ Scalar y
                       , TensorSpace w, Scalar w ~ Scalar y )
                => Haar_D¹ (Dual dn) (Tensor
                           (Scalar (DualVector y))
                            (DualVector y)
                            (Tensor (Scalar y) (DualVector u) w))
                 -> Haar_D¹ dn (y⊗u) -> w
         go (Haar_D¹ (Tensor a₀) δa) (Haar_D¹ f₀ δf)
               = ( (getLinearFunction applyTensorLinMap
                          (LinearMap a₀ :: (y⊗u)+>w)) CC.$ f₀ )
              ^+^ ( (getLinearFunction applyTensorLinMap $ LinearMap δa)
                              CC.$ (Tensor δf :: Haar0BiasTree dn y⊗u) )
                 
instance ∀ y dn .
           ( LinearSpace y, VAffineSpace y, Num' (Scalar y), ValidDualness dn
           , AffineSpace (DualVector y), Diff (DualVector y) ~ DualVector y ) 
             => LinearSpace (Haar_S¹ dn y) where
  type DualVector (Haar_S¹ dn y) = Haar_S¹ (Dual dn) (DualVector y)
  dualSpaceWitness = case ( dualSpaceWitness :: DualSpaceWitness y
                          , dualityWitness :: DualityWitness dn ) of
       (DualSpaceWitness, DualityWitness) -> DualSpaceWitness
  linearId = LinearMap hId
   where hId = case dualSpaceWitness :: DualSpaceWitness y of
          DualSpaceWitness
            -> Haar_S¹ (CC.fmap (CC.fmap . LinearFunction
                                          $ \s -> Haar_S¹ s) CC.$ getLinearMap
                                              (linearId :: Haar_D¹ dn y+>Haar_D¹ dn y))
  tensorId = LinearMap $ hId
   where hId :: ∀ w . (LinearSpace w, Scalar w ~ Scalar y)
               => Haar_S¹ (Dual dn)
                    (Tensor (Scalar (DualVector y))
                            (DualVector y)
                            (Tensor (Scalar y) (DualVector w)
                                (Tensor (Scalar y) (Haar_S¹ dn y) w)))
         hId = case ( dualSpaceWitness :: DualSpaceWitness y
                    , dualSpaceWitness :: DualSpaceWitness w ) of
          (DualSpaceWitness, DualSpaceWitness)
            -> Haar_S¹ (case tensorId :: (Haar_D¹ dn y⊗w)+>(Haar_D¹ dn y⊗w) of
                          LinearMap h₀ywId
                           -> CC.fmap (CC.fmap . CC.fmap . LinearFunction
                                       $ \(Tensor q) -> Tensor (Haar_S¹ q))
                                 CC.$ h₀ywId)
  applyDualVector = bilinearFunction $ \(Haar_S¹ a) (Haar_S¹ f)
      -> case (dualSpaceWitness @y, scalarSpaceWitness @y) of
           (DualSpaceWitness, ScalarSpaceWitness)
                -> (getLinearFunction applyDualVector a CC.$ f)
  applyTensorFunctional = bilinearFunction $ \(LinearMap a) (Tensor f) -> go a f
   where go :: ∀ u . (LinearSpace u, Scalar u ~ Scalar y)
             => Haar_S¹ (Dual dn) (DualVector y⊗DualVector u)
                 -> Haar_S¹ dn (y⊗u) -> Scalar y
         go (Haar_S¹ a) (Haar_S¹ f)
          = case ( dualSpaceWitness @y, dualSpaceWitness @u, scalarSpaceWitness @y ) of
           (DualSpaceWitness, DualSpaceWitness, ScalarSpaceWitness)
               -> (getLinearFunction applyDualVector
                              (Coercion CC.$ a) CC.$ f)
  applyLinear = bilinearFunction $ \(LinearMap a) f -> go a f
   where go :: ∀ w . (TensorSpace w, Scalar w ~ Scalar y)
                => Haar_S¹ (Dual dn) (Tensor (Scalar (DualVector y)) (DualVector y) w)
                      -> Haar_S¹ dn y -> w
         go (Haar_S¹ a) (Haar_S¹ f)
           = ( getLinearFunction applyLinear (LinearMap a :: Haar_D¹ dn y+>w) CC.$ f )
  applyTensorLinMap = bilinearFunction $ \(LinearMap a) (Tensor f) -> go a f
   where go :: ∀ u w . ( LinearSpace u, Scalar u ~ Scalar y
                       , TensorSpace w, Scalar w ~ Scalar y )
                => Haar_S¹ (Dual dn) (Tensor
                           (Scalar (DualVector y))
                            (DualVector y)
                            (Tensor (Scalar y) (DualVector u) w))
                 -> Haar_S¹ dn (y⊗u) -> w
         go (Haar_S¹ a) (Haar_S¹ f)
               = (getLinearFunction applyTensorLinMap $ LinearMap a)
                              CC.$ (Tensor f :: Haar_D¹ dn y⊗u)

instance (QC.Arbitrary y) => QC.Arbitrary (Haar_D¹ 'DistributionSpace y) where
  arbitrary = do
     Haar_D¹ <$> QC.arbitrary <*> genΔs
   where genΔs = QC.oneof
           [ pure HaarZero
           , HaarUnbiased <$> QC.arbitrary <*> genΔs <*> genΔs ]

instance (QC.Arbitrary y) => QC.Arbitrary (Haar_D¹ FunctionSpace y) where
  arbitrary = do
     n <- QC.getSize
          -- Magic numbers for the termination-probability: chosen empirically
          -- to get both approximately n as the expectation of the number of nodes
          -- in the function's tree representation, and a reasonable variance.
     Haar_D¹ <$> QC.arbitrary <*> genΔs (round . (*3) . (**0.22) $ fromIntegral n)
   where genΔs p'¹Terminate = QC.frequency
           [ (1, pure HaarZero)
           , (p'¹Terminate, HaarUnbiased <$> QC.arbitrary <*> genΔs pNext <*> genΔs pNext) ]
          where pNext = floor $ fromIntegral p'¹Terminate / 1.1

instance ( QC.Arbitrary (Tensor s x y), Scalar x ~ s )
               => QC.Arbitrary (Tensor s (Haar_D¹ FunctionSpace x) y) where
  arbitrary = Tensor <$> QC.arbitrary

#if !MIN_VERSION_linearmap_category(0,3,6)
instance (InnerSpace v, Scalar v ~ ℝ, TensorSpace v)
              => InnerSpace (Tensor ℝ ℝ v) where
  Tensor t <.> Tensor u = t <.> u
instance (Show v) => Show (Tensor ℝ ℝ v) where
  showsPrec p (Tensor t) = showParen (p>9) $ ("Tensor "++) . showsPrec 10 t
instance (QC.Arbitrary v, Scalar v ~ ℝ) => QC.Arbitrary (Tensor ℝ ℝ v) where
  arbitrary = Tensor <$> QC.arbitrary
  shrink (Tensor t) = Tensor <$> QC.shrink t
#endif
           
instance ( TensorSpace x, Scalar x ~ ℝ, AffineSpace x, Diff x ~ x, Needle x ~ x
         , TensorSpace y, Scalar y ~ ℝ, AffineSpace y, Diff y ~ y, Needle y ~ y
         , InnerSpace (Tensor ℝ x y) )
             => InnerSpace (Tensor ℝ (Haar_D¹ FunctionSpace x) y) where
  Tensor t <.> Tensor u = t <.> u

instance (Show y, Show (Diff y), Scalar y ~ ℝ)
             => Show (Tensor ℝ (Haar_D¹ dn ℝ) y) where
  showsPrec p (Tensor t) = showParen (p>9) $ ("Tensor "++) . showsPrec 10 t

instance (Show y, Show (Diff y), Scalar y ~ ℝ)
             => Show (Tensor ℝ (Haar_S¹ dn ℝ) y) where
  showsPrec p (Tensor t) = showParen (p>9) $ ("Tensor "++) . showsPrec 10 t
           
multiscaleDecompose :: VAffineSpace y => Haar D¹ y -> (y, (Haar D¹ y, Haar D¹ y))
multiscaleDecompose (Haar_D¹ y₀ HaarZero)
         = (y₀, zeroV)
multiscaleDecompose (Haar_D¹ y₀ (HaarUnbiased δlr fl fr))
         = (y₀, (Haar_D¹ (negateV δlr) fl, Haar_D¹ δlr fr))

-- | The size of the smallest features present in the function.
detailScale :: Haar D¹ y -> Needle D¹
detailScale (Haar_D¹ _ f) = go f
 where go HaarZero = 1
       go (HaarUnbiased _ l r) = min (go l) (go r)/2

haarFunctionGraph :: VAffineSpace y => Haar D¹ y -> [(D¹,y)]
haarFunctionGraph f = go id f []
 where go bounds (Haar_D¹ y₀ HaarZero) = (((,y₀) . bounds <$> [D¹ $ -1, D¹ 1])++)
       go bounds (Haar_D¹ y₀ (HaarUnbiased δlr fl fr))
        = go (bounds . view (re leftHalf)) (Haar_D¹ (y₀^-^δlr) fl)
           . go (bounds . view (re rightHalf)) (Haar_D¹ (y₀^+^δlr) fr)
