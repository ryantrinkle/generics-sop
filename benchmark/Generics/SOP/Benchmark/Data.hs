{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
module Generics.SOP.Benchmark.Data where

import Control.Applicative
import Data.Function (on)
import qualified GHC.Generics as GHC
import Generics.SOP
import Generics.SOP.TH
import qualified Generics.SOP.Type.Metadata as T
import Test.QuickCheck
import Test.QuickCheck.Gen
import Test.QuickCheck.Random
import Test.QuickCheck.Arbitrary (Arbitrary(..))
import Generic.Random


data GenericContext
  = SOPTHC -- SOP from Template Haskell and hand written combinator
  | SOPTH  -- SOP from Template Haskell
  | SOPDer -- SOP Derived via GHC.Generics
  | HW     -- Hand written
  | GHCGen -- GHC Generics
  | GHCDer -- GHC Derived instances

data TreeF (a :: GenericContext) = LeafF Int | NodeF (TreeF a) (TreeF a)
  deriving (GHC.Generic, Show, Eq)

instance Arbitrary (TreeF a) where
  arbitrary = genericArbitraryU'

newtype TreeSOPDer = TreeSOPDer (TreeF 'SOPDer) deriving (GHC.Generic)
newtype TreeSOPTH  = TreeSOPTH  (TreeF 'SOPTH)  deriving (GHC.Generic)
newtype TreeSOPTHC = TreeSOPTHC (TreeF 'SOPTHC) deriving (GHC.Generic)
newtype TreeHW     = TreeHW     (TreeF 'HW)     deriving (GHC.Generic)
newtype TreeGHCGen = TreeGHCGen (TreeF 'GHCGen) deriving (GHC.Generic)
newtype TreeGHCDer = TreeGHCDer (TreeF 'GHCDer) deriving (GHC.Generic)

instance Generic TreeSOPDer

deriveGeneric ''TreeSOPTH
deriveGeneric ''TreeSOPTHC

-- * Show

-- Generic show, kind of
gshow :: (Generic a, All2 Show (Code a)) => a -> String
gshow x = gshowS (from x)

gshowS :: (All2 Show xss) => SOP I xss -> String
gshowS (SOP (Z xs))  = gshowP xs
gshowS (SOP (S xss)) = gshowS (SOP xss)

gshowP :: (All Show xs) => NP I xs -> String
gshowP Nil         = ""
gshowP (I x :* xs) = show x ++ (gshowP xs)

-- Combinator version
gshow' :: (Generic a, All2 Show (Code a)) => a -> String
gshow' =
    concat
  . hcollapse
  . hcmap (Proxy :: Proxy Show) (mapIK show)
  . from

instance Show TreeSOPDer where show = gshow
instance Show TreeSOPTHC where show = gshow'
instance Show TreeSOPTH  where show = gshow
deriving instance Show TreeGHCDer

instance Show TreeHW where
  show (TreeHW t) = showHW t where
    showHW (LeafF x)   = show   x
    showHW (NodeF l r) = showHW l ++ showHW r

sample :: Int -> Gen a -> [a]
sample m g = [ gen n (n * n) g | n <- [0 .. m] ]
  where
    gen :: Int -> Int -> Gen a -> a
    gen p s (MkGen g) = g (mkQCGen p) s

-- * Eq

geq :: (Generic a, All2 Eq (Code a)) => a -> a -> Bool
geq = go `on` from
  where
    go :: forall xss. (All2 Eq xss, All SListI xss) => SOP I xss -> SOP I xss -> Bool
    go (SOP (Z xs))  (SOP (Z ys))  = and . hcollapse $ hcliftA2 p eq xs ys
    go (SOP (S xss)) (SOP (S yss)) = go (SOP xss) (SOP yss)
    go _             _             = False

    p :: Proxy Eq
    p = Proxy

    eq :: forall (a :: *). Eq a => I a -> I a -> K Bool a
    eq (I a) (I b) = K (a == b)

instance Eq TreeSOPDer where (==) = geq
instance Eq TreeSOPTH  where (==) = geq
deriving instance Eq TreeGHCDer
