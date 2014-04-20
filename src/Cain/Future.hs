------------------------------------------------------------------------------
-- Category Theory Applied to Functional Programming
--
-- 8.1 Future Work
------------------------------------------------------------------------------

{-# LANGUAGE InstanceSigs   #-}

module Cain.Future where

import Prelude ()

import qualified Cain.Categories (id, (.))

infixr 9 .

------------------------------------------------------------------------------
-- 8.1.3 Categories

-- The Category type class as defined in Control.Category.
class Category cat where
  id  :: cat a a
  (.) :: cat b c -> cat a b -> cat a c

-- Hask, the category of Haskell types and functions.
instance Category (->) where
  id :: a -> a
  id = Cain.Categories.id

  (.) :: (b -> c) -> (a -> b) -> a -> c
  (.) = (Cain.Categories..)

------------------------------------------------------------------------------
-- 8.1.5 Monoids

-- The Monoid type class as defined in Data.Monoid.
class Monoid a where
  mempty  :: a
  mappend :: a -> a -> a
