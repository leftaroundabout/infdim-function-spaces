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

data Dualness = FunctionSpace | DistributionSpace

type family Dual (dn :: Dualness) where
  Dual FunctionSpace = DistributionSpace
  Dual DistributionSpace = FunctionSpace

-- | Piecewise-constant functions on the unit interval whose integral is zero.
data Haar₀Tree (dn :: Dualness) (y :: *)
       = HaarZero
       | Haar₀ !y               -- ^ Offset-amplitude between the left and right half
               (Haar₀Tree dn y) -- ^ Left half of the function domain
               (Haar₀Tree dn y) -- ^ Right half, i.e. [0.5 .. 1[.
 deriving (Show)

type Haar₀ y = Haar₀Tree FunctionSpace y

data Haar_D¹ dn y = Haar_D¹
    { pwconst_D¹_offset :: !y
    , pwconst_D¹_variation :: Haar₀Tree dn y }
deriving instance (Show y, Show (Diff y)) => Show (Haar_D¹ dn y)

type instance Haar D¹ y = Haar_D¹ FunctionSpace y

fmapHaar₀Coeffs :: (TensorSpace y, TensorSpace z, Scalar y ~ Scalar z)
                    => (y-+>z) -> (Haar₀Tree dn y -+> Haar₀Tree dn z)
fmapHaar₀Coeffs f = LinearFunction go
 where go HaarZero = HaarZero
       go (Haar₀ δ l r) = Haar₀ (f CC.$ δ) (go l) (go r)

fmapHaarCoeffs :: (TensorSpace y, TensorSpace z, Scalar y ~ Scalar z)
                    => (y-+>z) -> (Haar_D¹ dn y -+> Haar_D¹ dn z)
fmapHaarCoeffs f = LinearFunction $
            \(Haar_D¹ y₀ δs) -> Haar_D¹ (f CC.$ y₀)
                      $ getLinearFunction (fmapHaar₀Coeffs f) δs

fzipHaar₀CoeffsWith :: ( TensorSpace x, TensorSpace y, TensorSpace z
                       , Scalar x ~ Scalar y, Scalar y ~ Scalar z )
                    => ((x,y)-+>z) -> ((Haar₀Tree dn x, Haar₀Tree dn y) -+> Haar₀Tree dn z)
fzipHaar₀CoeffsWith f = LinearFunction go
 where go (HaarZero, y) = getLinearFunction
               (fmapHaar₀Coeffs $ f CC.. LinearFunction (zeroV,)) $ y
       go (x, HaarZero) = getLinearFunction
               (fmapHaar₀Coeffs $ f CC.. LinearFunction (,zeroV)) $ x
       go (Haar₀ δx lx rx, Haar₀ δy ly ry)
            = Haar₀ (f CC.$ (δx,δy)) (go (lx,ly)) (go (rx,ry))

fzipHaarCoeffsWith :: ( TensorSpace x, TensorSpace y, TensorSpace z
                      , Scalar x ~ Scalar y, Scalar y ~ Scalar z )
                   => ((x,y)-+>z) -> ((Haar_D¹ dn x, Haar_D¹ dn y) -+> Haar_D¹ dn z)
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

instance AdditiveGroup y => AffineSpace (Haar₀Tree dn y) where
  type Diff (Haar₀Tree dn y) = Haar₀Tree dn y
  HaarZero .+^ f = f
  f .+^ HaarZero = f
  Haar₀ δlr₀ δsl₀ δsr₀ .+^ Haar₀ δlr₁ δsl₁ δsr₁
            = Haar₀ (δlr₀^+^δlr₁) (δsl₀.+^δsl₁) (δsr₀.+^δsr₁)
  HaarZero .-. HaarZero = HaarZero
  Haar₀ δlr₀ δsl₀ δsr₀ .-. Haar₀ δlr₁ δsl₁ δsr₁
            = Haar₀ (δlr₀^-^δlr₁) (δsl₀.-.δsl₁) (δsr₀.-.δsr₁)

instance AdditiveGroup y => AdditiveGroup (Haar₀Tree dn y) where
  (^+^) = (.+^)
  (^-^) = (.-.)
  zeroV = HaarZero
  negateV HaarZero = HaarZero
  negateV (Haar₀ δlr δsl δsr) = Haar₀ (negateV δlr) (negateV δsl) (negateV δsr)

instance VectorSpace y => VectorSpace (Haar₀Tree dn y) where
  type Scalar (Haar₀Tree dn y) = Scalar y
  _ *^ HaarZero = HaarZero
  μ *^ Haar₀ δlr δsl δsr = Haar₀ (μ*^δlr) (μ*^δsl) (μ*^δsr)
  
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

instance (InnerSpace y, Fractional (Scalar y)) => InnerSpace (Haar₀ y) where
  HaarZero <.> _ = 0
  _ <.> HaarZero = 0
  Haar₀ δlr₀ δsl₀ δsr₀ <.> Haar₀ δlr₁ δsl₁ δsr₁
            = δlr₀<.>δlr₁ + (δsl₀<.>δsl₁)/2 + (δsr₀<.>δsr₁)/2

-- | 𝓛² product on [-1…1] functions, i.e. @𝑓<.>𝑔 ⩵ ₋₁∫¹ d𝑥 𝑓(𝑥)·𝑔(𝑥)@
instance (InnerSpace y, Fractional (Scalar y), AffineSpace y, Diff y ~ y)
             => InnerSpace (Haar_D¹ FunctionSpace y) where
  Haar_D¹ y₀ δ₀ <.> Haar_D¹ y₁ δ₁ = 2*(y₀<.>y₁ + δ₀<.>δ₁)

instance ( VAffineSpace y
         , Semimanifold y, Needle y ~ Diff y
         , Semimanifold (Diff y), Needle (Diff y) ~ Diff y )
             => Semimanifold (Haar₀Tree dn y) where
  type Needle (Haar₀Tree dn y) = Haar₀Tree dn (Needle y)
  type Interior (Haar₀Tree dn y) = Haar₀Tree dn y
  translateP = Tagged (.+^)
  toInterior = Just
  fromInterior = id
instance ( VAffineSpace y
         , Semimanifold y, Needle y ~ Diff y
         , Semimanifold (Diff y), Needle (Diff y) ~ Diff y )
             => PseudoAffine (Haar₀Tree dn y) where
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
             => TensorSpace (Haar₀Tree dn y) where
  type TensorProduct (Haar₀Tree dn y) w = Haar₀Tree dn (y⊗w)
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
   where cftlp :: ∀ a b p . p (Haar₀Tree dn y) -> Coercion a b
                   -> Coercion (Haar₀Tree dn (Tensor ℝ (Diff y) a))
                               (Haar₀Tree dn (Tensor ℝ (Diff y) b))
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

data DualityWitness (dn :: Dualness) where
  DualityWitness :: (ValidDualness (Dual dn), Dual (Dual dn) ~ dn)
           => DualityWitness dn
class ValidDualness (dn :: Dualness) where
  dualityWitness :: DualityWitness dn
instance ValidDualness FunctionSpace where dualityWitness = DualityWitness
instance ValidDualness DistributionSpace where dualityWitness = DualityWitness

instance ∀ y dn . ( LinearSpace y, AffineSpace y
                  , Diff y ~ y, Needle y ~ y, Scalar y ~ ℝ
                  , Diff (DualVector y) ~ DualVector y, Needle (DualVector y) ~ DualVector y
                  , AffineSpace (DualVector y)
                  , ValidDualness dn )
             => LinearSpace (Haar₀Tree dn y) where
  type DualVector (Haar₀Tree dn y) = Haar₀Tree (Dual dn) (DualVector y)
  dualSpaceWitness = case ( dualSpaceWitness :: DualSpaceWitness y
                          , dualityWitness :: DualityWitness dn ) of
       (DualSpaceWitness, DualityWitness) -> DualSpaceWitness
  linearId = LinearMap hId
   where hId = case dualSpaceWitness :: DualSpaceWitness y of
          DualSpaceWitness
            -> Haar₀ (case linearId :: y+>y of
                        LinearMap yId
                            -> CC.fmap (LinearFunction
                                             $ \y -> Haar₀ y zeroV zeroV)
                                         CC.$ (Tensor yId :: DualVector y⊗y))
                     (fmapHaar₀Coeffs (CC.fmap . LinearFunction
                                        $ \l -> Haar₀ zeroV l zeroV) CC.$ hId)
                     (fmapHaar₀Coeffs (CC.fmap  . LinearFunction
                                        $ \r -> Haar₀ zeroV zeroV r) CC.$ hId)
  tensorId = LinearMap $ hId
   where hId :: ∀ w . (LinearSpace w, Scalar w ~ ℝ)
               => Haar₀Tree (Dual dn)
                    (Tensor (Scalar (DualVector y))
                            (DualVector y)
                            (Tensor Double (DualVector w) (Tensor ℝ (Haar₀Tree dn y) w)))
         hId = case ( dualSpaceWitness :: DualSpaceWitness y
                    , dualSpaceWitness :: DualSpaceWitness w ) of
          (DualSpaceWitness, DualSpaceWitness)
            -> Haar₀ (case tensorId :: (y⊗w)+>(y⊗w) of
                        LinearMap ywId
                            -> CC.fmap (CC.fmap $ LinearFunction
                                          $ \yw -> Tensor $ Haar₀ yw zeroV zeroV)
                                       CC.$ (Tensor ywId
                                              :: DualVector y⊗(DualVector w⊗(y⊗w))))
                     (fmapHaar₀Coeffs (CC.fmap . CC.fmap . LinearFunction
                            $ \(Tensor l) -> Tensor $ Haar₀ zeroV l zeroV) CC.$ hId)
                     (fmapHaar₀Coeffs (CC.fmap . CC.fmap . LinearFunction
                            $ \(Tensor r) -> Tensor $ Haar₀ zeroV zeroV r) CC.$ hId)
  applyDualVector = bilinearFunction $ \a f -> go a f
   where go :: Haar₀Tree (Dual dn) (DualVector y) -> Haar₀Tree dn y -> ℝ
         go HaarZero _ = zeroV
         go _ HaarZero = zeroV
         go (Haar₀ δa al ar) (Haar₀ δy fl fr)
          = case dualSpaceWitness :: DualSpaceWitness y of
           DualSpaceWitness
               -> (getLinearFunction applyDualVector δa CC.$ δy) + go al fl + go ar fr
  applyTensorFunctional = bilinearFunction $ \(LinearMap a) (Tensor f)
                        -> go a f
   where go :: ∀ u . (LinearSpace u, Scalar u ~ ℝ)
             => Haar₀Tree (Dual dn) (DualVector y⊗DualVector u) -> Haar₀Tree dn (y⊗u) -> ℝ
         go HaarZero _ = zeroV
         go _ HaarZero = zeroV
         go (Haar₀ (Tensor δa) al ar) (Haar₀ δy fl fr)
          = case dualSpaceWitness :: DualSpaceWitness y of
           DualSpaceWitness
               -> (getLinearFunction applyDualVector (LinearMap δa :: y+>DualVector u) CC.$ δy)
                    + go al fl + go ar fr
  applyLinear = bilinearFunction $ \(LinearMap a) f -> go a f
   where go :: ∀ w . (TensorSpace w, Scalar w ~ ℝ)
                => Haar₀Tree (Dual dn) (Tensor (Scalar (DualVector y)) (DualVector y) w)
                      -> Haar₀Tree dn y -> w
         go HaarZero _ = zeroV
         go _ HaarZero = zeroV
         go (Haar₀ (Tensor δa) al ar) (Haar₀ δy fl fr)
               = ( (getLinearFunction applyLinear (LinearMap δa :: y+>w)) CC.$ δy )
                   ^+^ go al fl ^+^ go ar fr
  applyTensorLinMap = bilinearFunction $ \(LinearMap a) (Tensor f)
                 -> go a f
   where go :: ∀ u w . (LinearSpace u, Scalar u ~ ℝ, TensorSpace w, Scalar w ~ ℝ)
                => Haar₀Tree (Dual dn) (Tensor
                           (Scalar (DualVector y))
                            (DualVector y)
                            (Tensor Double (DualVector u) w))
                 -> Haar₀Tree dn (y⊗u) -> w
         go HaarZero _ = zeroV
         go _ HaarZero = zeroV
         go (Haar₀ (Tensor δa) al ar) (Haar₀ δyu fl fr)
               = ( (getLinearFunction applyTensorLinMap
                          (LinearMap δa :: (y⊗u)+>w)) CC.$ δyu )
                   ^+^ go al fl ^+^ go ar fr
                 

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
           , (p'¹Terminate, Haar₀ <$> QC.arbitrary <*> genΔs pNext <*> genΔs pNext) ]
          where pNext = floor $ fromIntegral p'¹Terminate / 1.1
           
