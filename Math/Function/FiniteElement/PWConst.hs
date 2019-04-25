-- |
-- Module      : Math.Function.FiniteElement.PWConst
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

module Math.Function.FiniteElement.PWConst
        ( Haar, HaarSamplingDomain(..)
         -- * Utility
        , PowerOfTwo, getPowerOfTwo
        ) where

import Data.Manifold.Types
import Data.Manifold.PseudoAffine
import Data.Complex
import Data.List
import Data.AffineSpace
import Data.VectorSpace
import Math.LinearMap.Category
import qualified Control.Functor.Constrained as CC
import qualified Control.Arrow.Constrained as CC

import Control.Monad
import Control.Applicative
import Data.Tagged
import Data.Type.Coercion
import GHC.Generics

import qualified Test.QuickCheck as QC


-- | Piecewise-constant function with regular, power-of-two subdivisions, but
--   not necessarily with homogeneous resolution. 
--   The name refers to the fact that this type effectively contains a decomposition
--   in a basis of Haar wavelets.
type family Haar x y

-- | This constraint should in principle be just `AffineSpace`, but this conflicts
--   with the way the 'TensorSpace' class is set up, so we instead require
--   a vector space.
-- 
--   Ideally, the functions should ultimately be generalised to work even on
--   'PseudoAffine' manifolds.
type VAffineSpace y = (AffineSpace y, VectorSpace (Diff y), Diff y ~ y)

class HaarSamplingDomain x where
  evalHaarFunction :: VAffineSpace y
            => Haar x y -> x -> y
  homsampleHaarFunction :: (VAffineSpace y, Diff y ~ y, Fractional (Scalar y))
            => PowerOfTwo -> (x -> y) -> Haar x y

-- | Piecewise-constant functions on the unit interval whose integral is zero.
data Haar₀ y
       = HaarZero
       | Haar₀ !y        -- ^ Offset-amplitude between the left and right half
               (Haar₀ y) -- ^ Left half of the function domain
               (Haar₀ y) -- ^ Right half, i.e. [0.5 .. 1[.
 deriving (Show)

data Haar_D¹ y = Haar_D¹
    { pwconst_D¹_offset :: !y
    , pwconst_D¹_variation :: Haar₀ y }
deriving instance (Show y, Show (Diff y)) => Show (Haar_D¹ y)

type instance Haar D¹ y = Haar_D¹ y

fmapHaar₀Coeffs :: (TensorSpace y, TensorSpace z, Scalar y ~ Scalar z)
                    => (y-+>z) -> (Haar₀ y -+> Haar₀ z)
fmapHaar₀Coeffs f = LinearFunction go
 where go HaarZero = HaarZero
       go (Haar₀ δ l r) = Haar₀ (f CC.$ δ) (go l) (go r)

fmapHaarCoeffs :: (TensorSpace y, TensorSpace z, Scalar y ~ Scalar z)
                    => (y-+>z) -> (Haar_D¹ y -+> Haar_D¹ z)
fmapHaarCoeffs f = LinearFunction $
            \(Haar_D¹ y₀ δs) -> Haar_D¹ (f CC.$ y₀)
                      $ getLinearFunction (fmapHaar₀Coeffs f) δs

fzipHaar₀CoeffsWith :: ( TensorSpace x, TensorSpace y, TensorSpace z
                       , Scalar x ~ Scalar y, Scalar y ~ Scalar z )
                    => ((x,y)-+>z) -> ((Haar₀ x, Haar₀ y) -+> Haar₀ z)
fzipHaar₀CoeffsWith f = LinearFunction go
 where go (HaarZero, y) = getLinearFunction
               (fmapHaar₀Coeffs $ f CC.. LinearFunction (zeroV,)) $ y
       go (x, HaarZero) = getLinearFunction
               (fmapHaar₀Coeffs $ f CC.. LinearFunction (,zeroV)) $ x
       go (Haar₀ δx lx rx, Haar₀ δy ly ry)
            = Haar₀ (f CC.$ (δx,δy)) (go (lx,ly)) (go (rx,ry))

fzipHaarCoeffsWith :: ( TensorSpace x, TensorSpace y, TensorSpace z
                      , Scalar x ~ Scalar y, Scalar y ~ Scalar z )
                   => ((x,y)-+>z) -> ((Haar D¹ x, Haar D¹ y) -+> Haar D¹ z)
fzipHaarCoeffsWith f = LinearFunction
          $ \(Haar_D¹ x δxs, Haar_D¹ y δys)
               -> Haar_D¹ (f CC.$ (x,y))
                          (getLinearFunction (fzipHaar₀CoeffsWith f) (δxs,δys))
         
evalHaar_D¹ :: VAffineSpace y => Haar D¹ y -> D¹ -> y
evalHaar_D¹ (Haar_D¹ offs varis) x = offs .+^ evalVari varis x
 where evalVari HaarZero _ = zeroV
       evalVari (Haar₀ δlr lh rh) (D¹ x)
        | x<0        = evalVari lh (D¹ $ x*2 + 1) ^-^ δlr
        | otherwise  = evalVari rh (D¹ $ x*2 - 1) ^+^ δlr

newtype PowerOfTwo = TwoToThe { binaryExponent :: Int } deriving (Eq, Ord, Show)
getPowerOfTwo :: PowerOfTwo -> Integer
getPowerOfTwo (TwoToThe ex) = 2^ex

homsampleHaar_D¹ :: (VAffineSpace y, Diff y ~ y, Fractional (Scalar y))
            => PowerOfTwo -> (D¹ -> y) -> Haar D¹ y
homsampleHaar_D¹ (TwoToThe 0) f = Haar_D¹ (f $ D¹ 0) HaarZero
homsampleHaar_D¹ (TwoToThe i) f
   = case homsampleHaar_D¹ (TwoToThe $ i-1) <$> [f . leftHalf, f . rightHalf] of
       [Haar_D¹ y₀l sfl, Haar_D¹ y₀r sfr]
        -> Haar_D¹ ((y₀l^+^y₀r)^/2) $ Haar₀ ((y₀r^-^y₀l)^/2) sfl sfr

leftHalf, rightHalf :: D¹ -> D¹
leftHalf (D¹ x) = D¹ $ (x-1)/2
rightHalf (D¹ x) = D¹ $ (x+1)/2

instance HaarSamplingDomain D¹ where
  evalHaarFunction = evalHaar_D¹
  homsampleHaarFunction = homsampleHaar_D¹


instance QC.Arbitrary PowerOfTwo where
  arbitrary = do
    QC.Positive i <- QC.arbitrary
    return . TwoToThe . ceiling . logBase 2 $ fromInteger i
  shrink (TwoToThe i) = TwoToThe <$> [0 .. i-1]

instance AdditiveGroup y => AffineSpace (Haar₀ y) where
  type Diff (Haar₀ y) = Haar₀ y
  HaarZero .+^ f = f
  f .+^ HaarZero = f
  Haar₀ δlr₀ δsl₀ δsr₀ .+^ Haar₀ δlr₁ δsl₁ δsr₁
            = Haar₀ (δlr₀^+^δlr₁) (δsl₀.+^δsl₁) (δsr₀.+^δsr₁)
  HaarZero .-. HaarZero = HaarZero
  Haar₀ δlr₀ δsl₀ δsr₀ .-. Haar₀ δlr₁ δsl₁ δsr₁
            = Haar₀ (δlr₀^-^δlr₁) (δsl₀.-.δsl₁) (δsr₀.-.δsr₁)

instance AdditiveGroup y => AdditiveGroup (Haar₀ y) where
  (^+^) = (.+^)
  (^-^) = (.-.)
  zeroV = HaarZero
  negateV HaarZero = HaarZero
  negateV (Haar₀ δlr δsl δsr) = Haar₀ (negateV δlr) (negateV δsl) (negateV δsr)

instance VectorSpace y => VectorSpace (Haar₀ y) where
  type Scalar (Haar₀ y) = Scalar y
  _ *^ HaarZero = HaarZero
  μ *^ Haar₀ δlr δsl δsr = Haar₀ (μ*^δlr) (μ*^δsl) (μ*^δsr)
  
instance (VAffineSpace y) => AffineSpace (Haar_D¹ y) where
  type Diff (Haar_D¹ y) = Haar D¹ (Diff y)
  Haar_D¹ y₀ δ₀ .+^ Haar_D¹ y₁ δ₁ = Haar_D¹ (y₀.+^y₁) (δ₀.+^δ₁)
  Haar_D¹ y₀ δ₀ .-. Haar_D¹ y₁ δ₁ = Haar_D¹ (y₀.-.y₁) (δ₀.-.δ₁)

instance (VAffineSpace y, Diff y ~ y, AdditiveGroup y)
             => AdditiveGroup (Haar_D¹ y) where
  zeroV = Haar_D¹ zeroV zeroV
  (^+^) = (.+^)
  (^-^) = (.-.)
  negateV (Haar_D¹ y δ) = Haar_D¹ (negateV y) (negateV δ)

instance (VectorSpace y, AffineSpace y, Diff y ~ y)
             => VectorSpace (Haar_D¹ y) where
  type Scalar (Haar_D¹ y) = Scalar y
  μ *^ Haar_D¹ y δ = Haar_D¹ (μ*^y) (μ*^δ)

instance (InnerSpace y, Fractional (Scalar y)) => InnerSpace (Haar₀ y) where
  HaarZero <.> _ = 0
  _ <.> HaarZero = 0
  Haar₀ δlr₀ δsl₀ δsr₀ <.> Haar₀ δlr₁ δsl₁ δsr₁
            = δlr₀<.>δlr₁ + (δsl₀<.>δsl₁)/2 + (δsr₀<.>δsr₁)/2

-- | 𝓛² product on [-1…1] functions, i.e. @𝑓<.>𝑔 ⩵ ₋₁∫¹ d𝑥 𝑓(𝑥)·𝑔(𝑥)@
instance (InnerSpace y, Fractional (Scalar y), AffineSpace y, Diff y ~ y)
             => InnerSpace (Haar_D¹ y) where
  Haar_D¹ y₀ δ₀ <.> Haar_D¹ y₁ δ₁ = 2*(y₀<.>y₁ + δ₀<.>δ₁)

instance ( VAffineSpace y
         , Semimanifold y, Needle y ~ Diff y
         , Semimanifold (Diff y), Needle (Diff y) ~ Diff y )
             => Semimanifold (Haar₀ y) where
  type Needle (Haar₀ y) = Haar₀ (Needle y)
  type Interior (Haar₀ y) = Haar₀ y
  translateP = Tagged (.+^)
  toInterior = Just
  fromInterior = id
instance ( VAffineSpace y
         , Semimanifold y, Needle y ~ Diff y
         , Semimanifold (Diff y), Needle (Diff y) ~ Diff y )
             => PseudoAffine (Haar₀ y) where
  (.-~!) = (.-.)

instance ( VAffineSpace y
         , Semimanifold y, Needle y ~ Diff y
         , Semimanifold (Diff y), Needle (Diff y) ~ Diff y )
             => Semimanifold (Haar_D¹ y) where
  type Needle (Haar_D¹ y) = Haar D¹ (Needle y)
  type Interior (Haar_D¹ y) = Haar D¹ y
  translateP = Tagged (.+^)
  toInterior = Just
  fromInterior = id
instance ( VAffineSpace y
         , Semimanifold y, Needle y ~ Diff y
         , Semimanifold (Diff y), Needle (Diff y) ~ Diff y )
             => PseudoAffine (Haar_D¹ y) where
  (.-~!) = (.-.)

instance ∀ y . (TensorSpace y, AffineSpace y, Diff y ~ y, Needle y ~ y, Scalar y ~ ℝ)
             => TensorSpace (Haar₀ y) where
  type TensorProduct (Haar₀ y) w = Haar₀ (y⊗w)
  wellDefinedVector HaarZero = Just HaarZero
  wellDefinedVector (Haar₀ δ l r) = Haar₀ <$> wellDefinedVector δ
                                          <*> wellDefinedVector l
                                          <*> wellDefinedVector r
  wellDefinedTensor (Tensor HaarZero) = Just $ Tensor HaarZero
  wellDefinedTensor (Tensor (Haar₀ δ l r)) = Tensor <$>
                                   (Haar₀ <$> wellDefinedVector δ
                                          <*> wellDefinedVector l
                                          <*> wellDefinedVector r)
  scalarSpaceWitness = case scalarSpaceWitness :: ScalarSpaceWitness y of
     ScalarSpaceWitness -> ScalarSpaceWitness
  linearManifoldWitness = case linearManifoldWitness :: LinearManifoldWitness y of
     LinearManifoldWitness BoundarylessWitness -> LinearManifoldWitness BoundarylessWitness
  coerceFmapTensorProduct = cftlp
   where cftlp :: ∀ a b p . p (Haar₀ y) -> Coercion a b
                   -> Coercion (Haar₀ (Tensor ℝ (Diff y) a))
                               (Haar₀ (Tensor ℝ (Diff y) b))
         cftlp _ c = case CC.fmap c :: Coercion (Tensor ℝ y a) (Tensor ℝ y b) of
            Coercion -> Coercion
  zeroTensor = zeroV
  toFlatTensor = LinearFunction Tensor CC.. fmapHaar₀Coeffs toFlatTensor
  fromFlatTensor = fmapHaar₀Coeffs fromFlatTensor CC.. LinearFunction getTensorProduct
  addTensors (Tensor f) (Tensor g) = Tensor $ f^+^g
  scaleTensor = bilinearFunction $ \μ (Tensor f) -> Tensor $ μ*^f
  negateTensor = LinearFunction $ \(Tensor f) -> Tensor $ negateV f
  tensorProduct = bilinearFunction
         $ \f w -> Tensor $ fmapHaar₀Coeffs (LinearFunction $ \y -> y⊗w) CC.$ f
  transposeTensor = LinearFunction $
       \(Tensor (Haar₀ δyw δsl δsr))
           -> (CC.fmap (LinearFunction $ \δy -> Haar₀ δy zeroV zeroV)
                 CC.. transposeTensor CC.$ δyw)
             ^+^ (CC.fmap (LinearFunction $ \δysl -> Haar₀ zeroV δysl zeroV)
                 CC.. transposeTensor CC.$ Tensor δsl)
             ^+^ (CC.fmap (LinearFunction $ \δysr -> Haar₀ zeroV zeroV δysr)
                 CC.. transposeTensor CC.$ Tensor δsr)
  fmapTensor = bilinearFunction $ \a (Tensor f)
             -> Tensor $ fmapHaar₀Coeffs (CC.fmap a) CC.$ f
  fzipTensorWith = bilinearFunction $ \a (Tensor f, Tensor g)
             -> Tensor $ fzipHaar₀CoeffsWith (getLinearFunction fzipTensorWith a) CC.$ (f,g)
instance ∀ y . (TensorSpace y, AffineSpace y, Diff y ~ y, Needle y ~ y, Scalar y ~ ℝ)
             => TensorSpace (Haar_D¹ y) where
  type TensorProduct (Haar_D¹ y) w = Haar D¹ (y⊗w)
  wellDefinedVector (Haar_D¹ y₀ δs)
       = Haar_D¹ <$> wellDefinedVector y₀ <*> wellDefinedVector δs
  wellDefinedTensor (Tensor (Haar_D¹ y₀ δs))
       = Tensor <$> (Haar_D¹ <$> wellDefinedVector y₀ <*> wellDefinedVector δs)
  scalarSpaceWitness = case scalarSpaceWitness :: ScalarSpaceWitness y of
     ScalarSpaceWitness -> ScalarSpaceWitness
  linearManifoldWitness = case linearManifoldWitness :: LinearManifoldWitness y of
     LinearManifoldWitness BoundarylessWitness -> LinearManifoldWitness BoundarylessWitness
  coerceFmapTensorProduct = cftlp
   where cftlp :: ∀ a b p . p (Haar D¹ y) -> Coercion a b
                   -> Coercion (Haar D¹ (Tensor ℝ (Diff y) a))
                               (Haar D¹ (Tensor ℝ (Diff y) b))
         cftlp _ c = case CC.fmap c :: Coercion (Tensor ℝ y a) (Tensor ℝ y b) of
            Coercion -> Coercion
  zeroTensor = zeroV
  toFlatTensor = LinearFunction Tensor CC.. fmapHaarCoeffs toFlatTensor
  fromFlatTensor = fmapHaarCoeffs fromFlatTensor CC.. LinearFunction getTensorProduct
  addTensors (Tensor f) (Tensor g) = Tensor $ f^+^g
  scaleTensor = bilinearFunction $ \μ (Tensor f) -> Tensor $ μ*^f
  negateTensor = LinearFunction $ \(Tensor f) -> Tensor $ negateV f
  tensorProduct = bilinearFunction
         $ \f w -> Tensor $ fmapHaarCoeffs (LinearFunction $ \y -> y⊗w) CC.$ f
  transposeTensor = LinearFunction $
       \(Tensor (Haar_D¹ yw₀ δs))
           -> (CC.fmap (LinearFunction $ (`Haar_D¹`zeroV)) CC.. transposeTensor CC.$ yw₀)
  fmapTensor = bilinearFunction $ \a (Tensor f)
             -> Tensor $ fmapHaarCoeffs (CC.fmap a) CC.$ f
  fzipTensorWith = bilinearFunction $ \a (Tensor f, Tensor g)
             -> Tensor $ fzipHaarCoeffsWith (getLinearFunction fzipTensorWith a) CC.$ (f,g)

newtype Haar₀Dual y = Haar₀Dual {getHaar₀Dual :: Haar₀ y} deriving (Generic)

instance (VAffineSpace y) => AffineSpace (Haar₀Dual y) where
  type Diff (Haar₀Dual y) = Haar₀Dual (Diff y)
  Haar₀Dual p .+^ Haar₀Dual v = Haar₀Dual $ p.+^v
  Haar₀Dual p .-. Haar₀Dual q = Haar₀Dual $ p.-.q
instance (AdditiveGroup y) => AdditiveGroup (Haar₀Dual y)
instance (VectorSpace y) => VectorSpace (Haar₀Dual y)

instance ( VAffineSpace y, Semimanifold y, Needle y ~ Diff y
         , Semimanifold (Diff y), Needle (Diff y) ~ Diff y )
    => Semimanifold (Haar₀Dual y) where
  type Interior (Haar₀Dual y) = Haar₀Dual y; type Needle (Haar₀Dual y) = Haar₀Dual y
  translateP = Tagged (.+^); toInterior = Just; fromInterior = id
instance ( VAffineSpace y, Semimanifold y, Needle y ~ Diff y
         , Semimanifold (Diff y), Needle (Diff y) ~ Diff y )
    => PseudoAffine (Haar₀Dual y) where
  (.-~!) = (.-.)
  

newtype HaarD¹Dual y = HaarD¹Dual {getHaarD¹Dual :: Haar D¹ y} deriving (Generic)

instance (VAffineSpace y) => AffineSpace (HaarD¹Dual y) where
  type Diff (HaarD¹Dual y) = HaarD¹Dual (Diff y)
  HaarD¹Dual p .+^ HaarD¹Dual v = HaarD¹Dual $ p.+^v
  HaarD¹Dual p .-. HaarD¹Dual q = HaarD¹Dual $ p.-.q
instance (VAffineSpace y) => AdditiveGroup (HaarD¹Dual y)
instance (VAffineSpace y) => VectorSpace (HaarD¹Dual y)

instance ( VAffineSpace y, Semimanifold y, Needle y ~ Diff y
         , Semimanifold (Diff y), Needle (Diff y) ~ Diff y )
    => Semimanifold (HaarD¹Dual y) where
  type Interior (HaarD¹Dual y) = HaarD¹Dual y; type Needle (HaarD¹Dual y) = HaarD¹Dual y
  translateP = Tagged (.+^); toInterior = Just; fromInterior = id
instance ( VAffineSpace y, Semimanifold y, Needle y ~ Diff y
         , Semimanifold (Diff y), Needle (Diff y) ~ Diff y )
    => PseudoAffine (HaarD¹Dual y) where
  (.-~!) = (.-.)

instance ∀ y . (TensorSpace y, AffineSpace y, Diff y ~ y, Needle y ~ y, Scalar y ~ ℝ)
             => TensorSpace (Haar₀Dual y) where
  type TensorProduct (Haar₀Dual y) w = Haar₀Dual (y⊗w)
  wellDefinedVector (Haar₀Dual v) = Haar₀Dual <$> wellDefinedVector v
  wellDefinedTensor = wdt
   where wdt :: ∀ w . (TensorSpace w, Scalar w ~ ℝ)
                 => (Haar₀Dual y ⊗ w) -> Maybe (Haar₀Dual y ⊗ w)
         wdt (Tensor (Haar₀Dual t)) = Tensor . Haar₀Dual . getTensorProduct
              <$> wellDefinedTensor (Tensor t :: Haar₀ y ⊗ w)
  scalarSpaceWitness = case scalarSpaceWitness :: ScalarSpaceWitness y of
     ScalarSpaceWitness -> ScalarSpaceWitness
  linearManifoldWitness = case linearManifoldWitness :: LinearManifoldWitness y of
     LinearManifoldWitness BoundarylessWitness -> LinearManifoldWitness BoundarylessWitness
  coerceFmapTensorProduct = cftlp
   where cftlp :: ∀ a b p . p (Haar₀Dual y) -> Coercion a b
                   -> Coercion (Haar₀Dual (Tensor ℝ (Diff y) a))
                               (Haar₀Dual (Tensor ℝ (Diff y) b))
         cftlp _ c = case CC.fmap c :: Coercion (Tensor ℝ y a) (Tensor ℝ y b) of
            Coercion -> Coercion
  zeroTensor = zeroV
  toFlatTensor = LinearFunction (Tensor . Haar₀Dual)
                   CC.. fmapHaar₀Coeffs toFlatTensor
                   CC.. LinearFunction getHaar₀Dual
  fromFlatTensor = LinearFunction Haar₀Dual
                   CC.. fmapHaar₀Coeffs fromFlatTensor
                   CC.. LinearFunction (getHaar₀Dual . getTensorProduct)
  addTensors (Tensor f) (Tensor g) = Tensor $ f^+^g
  scaleTensor = bilinearFunction $ \μ (Tensor f) -> Tensor $ μ*^f
  negateTensor = LinearFunction $ \(Tensor f) -> Tensor $ negateV f
  tensorProduct = bilinearFunction
         $ \(Haar₀Dual f) w -> Tensor . Haar₀Dual
             $ fmapHaar₀Coeffs (LinearFunction $ \y -> y⊗w) CC.$ f
  transposeTensor = LinearFunction $
       \(Tensor (Haar₀Dual (Haar₀ δyw δsl δsr)))
           -> (CC.fmap (LinearFunction $ \δy -> Haar₀Dual $ Haar₀ δy zeroV zeroV)
                 CC.. transposeTensor CC.$ δyw)
             ^+^ (CC.fmap (LinearFunction $ \δysl -> Haar₀Dual $ Haar₀ zeroV δysl zeroV)
                 CC.. transposeTensor CC.$ Tensor δsl)
             ^+^ (CC.fmap (LinearFunction $ \δysr -> Haar₀Dual $ Haar₀ zeroV zeroV δysr)
                 CC.. transposeTensor CC.$ Tensor δsr)
  fmapTensor = bilinearFunction $ \a (Tensor (Haar₀Dual f))
             -> Tensor . Haar₀Dual $ fmapHaar₀Coeffs (CC.fmap a) CC.$ f
  fzipTensorWith = bilinearFunction $ \a (Tensor (Haar₀Dual f), Tensor (Haar₀Dual g))
             -> Tensor . Haar₀Dual
                  $ fzipHaar₀CoeffsWith (getLinearFunction fzipTensorWith a) CC.$ (f,g)

instance ∀ y . (TensorSpace y, AffineSpace y, Diff y ~ y, Needle y ~ y, Scalar y ~ ℝ)
             => TensorSpace (HaarD¹Dual y) where
  type TensorProduct (HaarD¹Dual y) w = HaarD¹Dual (y⊗w)
  wellDefinedVector (HaarD¹Dual v) = HaarD¹Dual <$> wellDefinedVector v
  wellDefinedTensor = wdt
   where wdt :: ∀ w . (TensorSpace w, Scalar w ~ ℝ)
                 => (HaarD¹Dual y ⊗ w) -> Maybe (HaarD¹Dual y ⊗ w)
         wdt (Tensor (HaarD¹Dual t)) = Tensor . HaarD¹Dual . getTensorProduct
              <$> wellDefinedTensor (Tensor t :: Haar D¹ y ⊗ w)
  scalarSpaceWitness = case scalarSpaceWitness :: ScalarSpaceWitness y of
     ScalarSpaceWitness -> ScalarSpaceWitness
  linearManifoldWitness = case linearManifoldWitness :: LinearManifoldWitness y of
     LinearManifoldWitness BoundarylessWitness -> LinearManifoldWitness BoundarylessWitness
  coerceFmapTensorProduct = cftlp
   where cftlp :: ∀ a b p . p (HaarD¹Dual y) -> Coercion a b
                   -> Coercion (HaarD¹Dual (Tensor ℝ (Diff y) a))
                               (HaarD¹Dual (Tensor ℝ (Diff y) b))
         cftlp _ c = case CC.fmap c :: Coercion (Tensor ℝ y a) (Tensor ℝ y b) of
            Coercion -> Coercion
  zeroTensor = zeroV
  toFlatTensor = LinearFunction (Tensor . HaarD¹Dual)
                   CC.. fmapHaarCoeffs toFlatTensor
                   CC.. LinearFunction getHaarD¹Dual
  fromFlatTensor = LinearFunction HaarD¹Dual
                   CC.. fmapHaarCoeffs fromFlatTensor
                   CC.. LinearFunction (getHaarD¹Dual . getTensorProduct)
  addTensors (Tensor f) (Tensor g) = Tensor $ f^+^g
  scaleTensor = bilinearFunction $ \μ (Tensor f) -> Tensor $ μ*^f
  negateTensor = LinearFunction $ \(Tensor f) -> Tensor $ negateV f
  tensorProduct = bilinearFunction
         $ \(HaarD¹Dual f) w -> Tensor . HaarD¹Dual
             $ fmapHaarCoeffs (LinearFunction $ \y -> y⊗w) CC.$ f
  transposeTensor = LinearFunction $
       \(Tensor (HaarD¹Dual (Haar_D¹ yw₀ δs)))
           -> (CC.fmap (LinearFunction $ HaarD¹Dual . (`Haar_D¹`zeroV))
                    CC.. transposeTensor CC.$ yw₀)
  fmapTensor = bilinearFunction $ \a (Tensor (HaarD¹Dual f))
             -> Tensor . HaarD¹Dual $ fmapHaarCoeffs (CC.fmap a) CC.$ f
  fzipTensorWith = bilinearFunction $ \a (Tensor (HaarD¹Dual f), Tensor (HaarD¹Dual g))
             -> Tensor . HaarD¹Dual
                  $ fzipHaarCoeffsWith (getLinearFunction fzipTensorWith a) CC.$ (f,g)


instance (QC.Arbitrary y, QC.Arbitrary (Diff y))
               => QC.Arbitrary (Haar_D¹ y) where
  arbitrary = do
     n <- QC.getSize
          -- Magic numbers for the termination-probability: chosen empirically
          -- to get both approximately n as the expectation of the number of nodes
          -- in the function's tree representation, and a reasonable variance.
     Haar_D¹ <$> QC.arbitrary <*> genΔs (round . (*3) . (**0.22) $ fromIntegral n)
   where genΔs p'¹Terminate = QC.frequency
           [ (1, pure HaarZero)
           , (p'¹Terminate, Haar₀ <$> QC.arbitrary <*> genΔs pNext <*> genΔs pNext) ]
          where pNext = floor $ fromIntegral p'¹Terminate / 1.1
           
