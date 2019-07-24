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

type instance Haar D¹ y = Haar_D¹ FunctionSpace y

instance CC.Functor (Haar0BiasTree dn) (LinearFunction ℝ) (LinearFunction ℝ) where
  fmap f = LinearFunction go
   where go HaarZero = HaarZero
         go (HaarUnbiased δ l r) = HaarUnbiased (f CC.$ δ) (go l) (go r)

instance CC.Functor (Haar_D¹ dn) (LinearFunction ℝ) (LinearFunction ℝ) where
  fmap = fmapLFH
   where fmapLFH :: ∀ y z . (TensorSpace y, TensorSpace z, Scalar y ~ ℝ, Scalar z ~ ℝ)
             => (y-+>z) -> (Haar_D¹ dn y-+>Haar_D¹ dn z)
         fmapLFH f = case (linearManifoldWitness @z, linearManifoldWitness @y) of
          (LinearManifoldWitness _, LinearManifoldWitness _) ->
           LinearFunction $
            \(Haar_D¹ y₀ δs) -> Haar_D¹ (f CC.$ y₀)
                      $ getLinearFunction (CC.fmap f) δs

instance CC.Monoidal (Haar0BiasTree dn) (LinearFunction ℝ) (LinearFunction ℝ) where
  pureUnit = LinearFunction $ \Origin -> HaarZero
  fzipWith = fzwLFH
   where fzwLFH :: ∀ a b c .
                   ( TensorSpace a, TensorSpace b, TensorSpace c
                   , Scalar a ~ ℝ, Scalar b ~ ℝ, Scalar c ~ ℝ )
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

instance CC.Monoidal (Haar_D¹ dn) (LinearFunction ℝ) (LinearFunction ℝ) where
  pureUnit = LinearFunction $ \Origin -> zeroV
  fzipWith = fzwLFH
   where fzwLFH :: ∀ x y z dn . 
                      ( TensorSpace x, TensorSpace y, TensorSpace z
                      , Scalar x ~ ℝ, Scalar y ~ ℝ, Scalar z ~ ℝ )
                   => ((x,y)-+>z) -> ((Haar_D¹ dn x, Haar_D¹ dn y) -+> Haar_D¹ dn z)
         fzwLFH = case ( linearManifoldWitness @x
                       , linearManifoldWitness @y
                       , linearManifoldWitness @z ) of
          (LinearManifoldWitness _, LinearManifoldWitness _, LinearManifoldWitness _)
             -> \f -> LinearFunction
                   $ \(Haar_D¹ x δxs, Haar_D¹ y δys)
                        -> Haar_D¹ (f CC.$ (x,y))
                                   (getLinearFunction (CC.fzipWith f) (δxs,δys))
         
evalHaar_D¹ :: VAffineSpace y => Haar D¹ y -> D¹ -> y
evalHaar_D¹ (Haar_D¹ offs varis) x = offs .+^ evalVari varis x
 where evalVari HaarZero _ = zeroV
       evalVari (HaarUnbiased δlr lh rh) p = case p^.halves of
        Left pl  -> evalVari lh pl ^-^ δlr
        Right pr -> evalVari rh pr ^+^ δlr

homsampleHaar_D¹ :: (VAffineSpace y, Diff y ~ y, Fractional (Scalar y))
            => PowerOfTwo -> (D¹ -> y) -> Haar D¹ y
homsampleHaar_D¹ (TwoToThe 0) f = Haar_D¹ (f $ D¹ 0) HaarZero
homsampleHaar_D¹ (TwoToThe i) f
   = case homsampleHaar_D¹ (TwoToThe $ i-1) <$> [ f . view (re leftHalf)
                                                , f . view (re rightHalf) ] of
       [Haar_D¹ y₀l sfl, Haar_D¹ y₀r sfr]
        -> Haar_D¹ ((y₀l^+^y₀r)^/2) $ HaarUnbiased ((y₀r^-^y₀l)^/2) sfl sfr

boxDistributionD¹ :: (VectorSpace y, Scalar y ~ ℝ)
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
                            $ y^*if r>0 then l/(l-r) else 1
       Haar_D¹ wr rstru = boxDistributionD¹ (D¹ $ max 0 l*2 - 1, D¹ $ r*2 - 1)
                            $ y^*if l<0 then r/(r-l) else 1

diracD¹ :: D¹ -> DualVector (Haar D¹ ℝ)
diracD¹ x₀ = boxDistributionD¹ (x₀,x₀) 1


-- | Given a function \(f\) and an interval \((\ell,r)\), yield the integral
--   \(\backslash x \mapsto \int\limits_{\ell}^r \mathrm{d}t\: f(t)\).
integrateHaarFunction :: (VectorSpace y, Scalar y ~ ℝ) => Haar D¹ y -> (D¹,D¹) -> y
integrateHaarFunction f = \(l,r) -> antideriv f r ^+^ c l
 where c (D¹ 0) = case f of Haar_D¹ _ (HaarUnbiased yr _ _) -> yr
                            _                               -> zeroV
       c l = negateV $ antideriv f l
       antideriv (Haar_D¹ y₀ ff) p@(D¹ x) = x*^y₀ ^+^ down ff p^/2
       down HaarZero _ = zeroV
       down (HaarUnbiased δlr fl fr) p = ( case p^.halves of
        Left pl  -> antideriv (Haar_D¹ (negateV δlr) fl) pl
        Right pr -> antideriv (Haar_D¹          δlr  fr) pr ) ^-^ δlr


instance HaarSamplingDomain D¹ where
  evalHaarFunction = evalHaar_D¹
  homsampleHaarFunction = homsampleHaar_D¹
  dirac = diracD¹


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
  
instance (VAffineSpace y) => AffineSpace (Haar_D¹ dn y) where
  type Diff (Haar_D¹ dn y) = Haar_D¹ dn (Diff y)
  Haar_D¹ y₀ δ₀ .+^ Haar_D¹ y₁ δ₁ = Haar_D¹ (y₀.+^y₁) (δ₀.+^δ₁)
  Haar_D¹ y₀ δ₀ .-. Haar_D¹ y₁ δ₁ = Haar_D¹ (y₀.-.y₁) (δ₀.-.δ₁)

instance (VAffineSpace y, Diff y ~ y, AdditiveGroup y)
             => AdditiveGroup (Haar_D¹ dn y) where
  zeroV = Haar_D¹ zeroV zeroV
  (^+^) = (.+^)
  (^-^) = (.-.)
  negateV (Haar_D¹ y δ) = Haar_D¹ (negateV y) (negateV δ)

instance (VectorSpace y, AffineSpace y, Diff y ~ y)
             => VectorSpace (Haar_D¹ dn y) where
  type Scalar (Haar_D¹ dn y) = Scalar y
  μ *^ Haar_D¹ y δ = Haar_D¹ (μ*^y) (μ*^δ)

instance (InnerSpace y, Fractional (Scalar y)) => InnerSpace (HaarUnbiased y) where
  HaarZero <.> _ = 0
  _ <.> HaarZero = 0
  HaarUnbiased δlr₀ δsl₀ δsr₀ <.> HaarUnbiased δlr₁ δsl₁ δsr₁
            = δlr₀<.>δlr₁ + (δsl₀<.>δsl₁)/2 + (δsr₀<.>δsr₁)/2

-- | 𝓛² product on [-1…1] functions, i.e. @𝑓<.>𝑔 ⩵ ₋₁∫¹ d𝑥 𝑓(𝑥)·𝑔(𝑥)@
instance (InnerSpace y, Fractional (Scalar y), AffineSpace y, Diff y ~ y)
             => InnerSpace (Haar_D¹ FunctionSpace y) where
  Haar_D¹ y₀ δ₀ <.> Haar_D¹ y₁ δ₁ = 2*(y₀<.>y₁ + δ₀<.>δ₁)

instance ( VAffineSpace y
         , Semimanifold y, Needle y ~ Diff y
         , Semimanifold (Diff y), Needle (Diff y) ~ Diff y )
             => Semimanifold (Haar0BiasTree dn y) where
  type Needle (Haar0BiasTree dn y) = Haar0BiasTree dn (Needle y)
  type Interior (Haar0BiasTree dn y) = Haar0BiasTree dn y
  translateP = Tagged (.+^)
  toInterior = Just
  fromInterior = id
instance ( VAffineSpace y
         , Semimanifold y, Needle y ~ Diff y
         , Semimanifold (Diff y), Needle (Diff y) ~ Diff y )
             => PseudoAffine (Haar0BiasTree dn y) where
  (.-~!) = (.-.)

instance ( VAffineSpace y
         , Semimanifold y, Needle y ~ Diff y
         , Semimanifold (Diff y), Needle (Diff y) ~ Diff y )
             => Semimanifold (Haar_D¹ dn y) where
  type Needle (Haar_D¹ dn y) = Haar_D¹ dn (Needle y)
  type Interior (Haar_D¹ dn y) = Haar_D¹ dn y
  translateP = Tagged (.+^)
  toInterior = Just
  fromInterior = id
instance ( VAffineSpace y
         , Semimanifold y, Needle y ~ Diff y
         , Semimanifold (Diff y), Needle (Diff y) ~ Diff y )
             => PseudoAffine (Haar_D¹ dn y) where
  (.-~!) = (.-.)

instance ∀ y dn . (TensorSpace y, AffineSpace y, Diff y ~ y, Needle y ~ y, Scalar y ~ ℝ)
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
                   -> Coercion (Haar0BiasTree dn (Tensor ℝ (Diff y) a))
                               (Haar0BiasTree dn (Tensor ℝ (Diff y) b))
         cftlp _ c = case CC.fmap c :: Coercion (Tensor ℝ y a) (Tensor ℝ y b) of
            Coercion -> Coercion
  zeroTensor = zeroV
  toFlatTensor = LinearFunction Tensor CC.. CC.fmap toFlatTensor
  fromFlatTensor = CC.fmap fromFlatTensor CC.. LinearFunction getTensorProduct
  addTensors (Tensor f) (Tensor g) = Tensor $ f^+^g
  scaleTensor = bilinearFunction $ \μ (Tensor f) -> Tensor $ μ*^f
  negateTensor = LinearFunction $ \(Tensor f) -> Tensor $ negateV f
  tensorProduct = bilinearFunction
         $ \f w -> Tensor $ CC.fmap (LinearFunction $ \y -> y⊗w) CC.$ f
  transposeTensor = LinearFunction $
       \(Tensor (HaarUnbiased δyw δsl δsr))
           -> (CC.fmap (LinearFunction $ \δy -> HaarUnbiased δy zeroV zeroV)
                 CC.. transposeTensor CC.$ δyw)
             ^+^ (CC.fmap (LinearFunction $ \δysl -> HaarUnbiased zeroV δysl zeroV)
                 CC.. transposeTensor CC.$ Tensor δsl)
             ^+^ (CC.fmap (LinearFunction $ \δysr -> HaarUnbiased zeroV zeroV δysr)
                 CC.. transposeTensor CC.$ Tensor δsr)
  fmapTensor = bilinearFunction $ \a (Tensor f)
             -> Tensor $ CC.fmap (CC.fmap a) CC.$ f
  fzipTensorWith = bilinearFunction $ \a (Tensor f, Tensor g)
             -> Tensor $ CC.fzipWith (getLinearFunction fzipTensorWith a) CC.$ (f,g)
instance ∀ y dn
         . (TensorSpace y, AffineSpace y, Diff y ~ y, Needle y ~ y, Scalar y ~ ℝ)
             => TensorSpace (Haar_D¹ dn y) where
  type TensorProduct (Haar_D¹ dn y) w = Haar_D¹ dn (y⊗w)
  wellDefinedVector (Haar_D¹ y₀ δs)
       = Haar_D¹ <$> wellDefinedVector y₀ <*> wellDefinedVector δs
  wellDefinedTensor (Tensor (Haar_D¹ y₀ δs))
       = Tensor <$> (Haar_D¹ <$> wellDefinedVector y₀ <*> wellDefinedVector δs)
  scalarSpaceWitness = case scalarSpaceWitness :: ScalarSpaceWitness y of
     ScalarSpaceWitness -> ScalarSpaceWitness
  linearManifoldWitness = case linearManifoldWitness :: LinearManifoldWitness y of
     LinearManifoldWitness BoundarylessWitness -> LinearManifoldWitness BoundarylessWitness
  coerceFmapTensorProduct = cftlp
   where cftlp :: ∀ a b p . p (Haar_D¹ dn y) -> Coercion a b
                   -> Coercion (Haar_D¹ dn (Tensor ℝ (Diff y) a))
                               (Haar_D¹ dn (Tensor ℝ (Diff y) b))
         cftlp _ c = case CC.fmap c :: Coercion (Tensor ℝ y a) (Tensor ℝ y b) of
            Coercion -> Coercion
  zeroTensor = zeroV
  toFlatTensor = LinearFunction Tensor CC.. CC.fmap toFlatTensor
  fromFlatTensor = CC.fmap fromFlatTensor CC.. LinearFunction getTensorProduct
  addTensors (Tensor f) (Tensor g) = Tensor $ f^+^g
  scaleTensor = bilinearFunction $ \μ (Tensor f) -> Tensor $ μ*^f
  negateTensor = LinearFunction $ \(Tensor f) -> Tensor $ negateV f
  tensorProduct = bilinearFunction
         $ \f w -> Tensor $ CC.fmap (LinearFunction $ \y -> y⊗w) CC.$ f
  transposeTensor = LinearFunction $
       \(Tensor (Haar_D¹ yw₀ δs))
           -> (CC.fmap (LinearFunction $ (`Haar_D¹`zeroV)) CC.. transposeTensor CC.$ yw₀)
             ^+^ (CC.fmap (LinearFunction $ Haar_D¹ zeroV)
                   CC.. transposeTensor CC.$ Tensor δs)
  fmapTensor = bilinearFunction $ \a (Tensor f)
             -> Tensor $ CC.fmap (CC.fmap a) CC.$ f
  fzipTensorWith = bilinearFunction $ \a (Tensor f, Tensor g)
             -> Tensor $ CC.fzipWith (getLinearFunction fzipTensorWith a) CC.$ (f,g)




instance ∀ y dn . ( LinearSpace y, AffineSpace y
                  , Diff y ~ y, Needle y ~ y, Scalar y ~ ℝ
                  , Diff (DualVector y) ~ DualVector y, Needle (DualVector y) ~ DualVector y
                  , AffineSpace (DualVector y)
                  , ValidDualness dn )
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
   where hId :: ∀ w . (LinearSpace w, Scalar w ~ ℝ)
               => Haar0BiasTree (Dual dn)
                    (Tensor (Scalar (DualVector y))
                            (DualVector y)
                            (Tensor Double (DualVector w) (Tensor ℝ (Haar0BiasTree dn y) w)))
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
   where go :: Haar0BiasTree (Dual dn) (DualVector y) -> Haar0BiasTree dn y -> ℝ
         go HaarZero _ = zeroV
         go _ HaarZero = zeroV
         go (HaarUnbiased δa al ar) (HaarUnbiased δy fl fr)
          = case dualSpaceWitness :: DualSpaceWitness y of
           DualSpaceWitness
               -> (getLinearFunction applyDualVector δa CC.$ δy) + go al fl + go ar fr
  applyTensorFunctional = bilinearFunction $ \(LinearMap a) (Tensor f)
                        -> go a f
   where go :: ∀ u . (LinearSpace u, Scalar u ~ ℝ)
             => Haar0BiasTree (Dual dn) (DualVector y⊗DualVector u) -> Haar0BiasTree dn (y⊗u) -> ℝ
         go HaarZero _ = zeroV
         go _ HaarZero = zeroV
         go (HaarUnbiased (Tensor δa) al ar) (HaarUnbiased δy fl fr)
          = case dualSpaceWitness :: DualSpaceWitness y of
           DualSpaceWitness
               -> (getLinearFunction applyDualVector (LinearMap δa :: y+>DualVector u) CC.$ δy)
                    + go al fl + go ar fr
  applyLinear = bilinearFunction $ \(LinearMap a) f -> go a f
   where go :: ∀ w . (TensorSpace w, Scalar w ~ ℝ)
                => Haar0BiasTree (Dual dn) (Tensor (Scalar (DualVector y)) (DualVector y) w)
                      -> Haar0BiasTree dn y -> w
         go HaarZero _ = zeroV
         go _ HaarZero = zeroV
         go (HaarUnbiased (Tensor δa) al ar) (HaarUnbiased δy fl fr)
               = ( (getLinearFunction applyLinear (LinearMap δa :: y+>w)) CC.$ δy )
                   ^+^ go al fl ^+^ go ar fr
  applyTensorLinMap = bilinearFunction $ \(LinearMap a) (Tensor f)
                 -> go a f
   where go :: ∀ u w . (LinearSpace u, Scalar u ~ ℝ, TensorSpace w, Scalar w ~ ℝ)
                => Haar0BiasTree (Dual dn) (Tensor
                           (Scalar (DualVector y))
                            (DualVector y)
                            (Tensor Double (DualVector u) w))
                 -> Haar0BiasTree dn (y⊗u) -> w
         go HaarZero _ = zeroV
         go _ HaarZero = zeroV
         go (HaarUnbiased (Tensor δa) al ar) (HaarUnbiased δyu fl fr)
               = ( (getLinearFunction applyTensorLinMap
                          (LinearMap δa :: (y⊗u)+>w)) CC.$ δyu )
                   ^+^ go al fl ^+^ go ar fr
                 
instance ∀ y dn . ( LinearSpace y, AffineSpace y
                  , Diff y ~ y, Needle y ~ y, Scalar y ~ ℝ
                  , Diff (DualVector y) ~ DualVector y, Needle (DualVector y) ~ DualVector y
                  , AffineSpace (DualVector y)
                  , ValidDualness dn )
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
   where hId :: ∀ w . (LinearSpace w, Scalar w ~ ℝ)
               => Haar_D¹ (Dual dn)
                    (Tensor (Scalar (DualVector y))
                            (DualVector y)
                            (Tensor Double (DualVector w) (Tensor ℝ (Haar_D¹ dn y) w)))
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
      -> case dualSpaceWitness :: DualSpaceWitness y of
           DualSpaceWitness -> (getLinearFunction applyDualVector a₀ CC.$ f₀)
                             + (getLinearFunction applyDualVector δa CC.$ δf)
  applyTensorFunctional = bilinearFunction $ \(LinearMap a) (Tensor f) -> go a f
   where go :: ∀ u . (LinearSpace u, Scalar u ~ ℝ)
             => Haar_D¹ (Dual dn) (DualVector y⊗DualVector u) -> Haar_D¹ dn (y⊗u) -> ℝ
         go (Haar_D¹ (Tensor a₀) δa) (Haar_D¹ f₀ δf)
          = case ( dualSpaceWitness :: DualSpaceWitness y
                 , dualSpaceWitness :: DualSpaceWitness u ) of
           (DualSpaceWitness, DualSpaceWitness)
               -> (getLinearFunction applyDualVector (LinearMap a₀ :: y+>DualVector u)
                                                              CC.$ f₀)
                + (getLinearFunction applyDualVector
                              (Coercion CC.$ δa) CC.$ δf)
  applyLinear = bilinearFunction $ \(LinearMap a) f -> go a f
   where go :: ∀ w . (TensorSpace w, Scalar w ~ ℝ)
                => Haar_D¹ (Dual dn) (Tensor (Scalar (DualVector y)) (DualVector y) w)
                      -> Haar_D¹ dn y -> w
         go (Haar_D¹ (Tensor a₀) δa) (Haar_D¹ f₀ δf)
           = ( (getLinearFunction applyLinear (LinearMap a₀ :: y+>w)) CC.$ f₀ )
          ^+^ ( getLinearFunction applyLinear (LinearMap δa :: Haar0BiasTree dn y+>w) CC.$ δf )
  applyTensorLinMap = bilinearFunction $ \(LinearMap a) (Tensor f) -> go a f
   where go :: ∀ u w . (LinearSpace u, Scalar u ~ ℝ, TensorSpace w, Scalar w ~ ℝ)
                => Haar_D¹ (Dual dn) (Tensor
                           (Scalar (DualVector y))
                            (DualVector y)
                            (Tensor Double (DualVector u) w))
                 -> Haar_D¹ dn (y⊗u) -> w
         go (Haar_D¹ (Tensor a₀) δa) (Haar_D¹ f₀ δf)
               = ( (getLinearFunction applyTensorLinMap
                          (LinearMap a₀ :: (y⊗u)+>w)) CC.$ f₀ )
              ^+^ ( (getLinearFunction applyTensorLinMap $ LinearMap δa)
                              CC.$ (Tensor δf :: Haar0BiasTree dn y⊗u) )

instance (QC.Arbitrary y, QC.Arbitrary (Diff y))
               => QC.Arbitrary (Haar_D¹ FunctionSpace y) where
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
