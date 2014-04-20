------------------------------------------------------------------------------
-- Category Theory Applied to Functional Programming
--
-- Chapter 4 Functors
------------------------------------------------------------------------------

{-# LANGUAGE InstanceSigs   #-}

module Cain.Functors where

import Prelude ()

import Cain.Categories ((.))
import Cain.Constructions (Either (Left, Right))

-- The map function as defined in GHC.Base.
map :: (a -> b) -> [a] -> [b]
map _ []     = []
map f (x:xs) = f x : fmap f xs

-- An alternative “map” function.
map' :: (a -> b) -> [a] -> [b]
map' _ []     = []
map' f (x:xs) = f x : f x : fmap f xs

------------------------------------------------------------------------------
-- 4.2 Functors in Haskell

-- The Functor type class as defined in GHC.Base.
class Functor f where
  fmap :: (a -> b) -> f a -> f b

-- The Identity type.
newtype Identity a = Identity {unIdentity :: a}

-- The Identity functor.
instance Functor Identity where
  fmap :: (a -> b) -> Identity a -> Identity b
  fmap f (Identity x) = Identity (f x)

-- The Maybe type as defined in Data.Maybe.
data Maybe a = Nothing | Just a

-- The Maybe functor as defined in Data.Maybe.
instance Functor Maybe where
  fmap :: (a -> b) -> Maybe a -> Maybe b
  fmap _ Nothing  = Nothing
  fmap f (Just x) = Just (f x)

-- The [] functor as defined in GHC.Base.
instance Functor [] where -- Defined in GHC.Base
  fmap :: (a -> b) -> [a] -> [b]
  fmap = map

-- Or:

  -- fmap _ []     = []
  -- fmap f (x:xs) = f x : fmap f xs

-- The ((,) a) functor as defined in GHC.Base.
instance Functor ((,) a) where
  fmap :: (b -> c) -> (a,b) -> (a,c)
  fmap f (x,y) = (x, f y)

-- The (Either a) functor as defined in Data.Either.
instance Functor (Either a) where
  fmap :: (b -> c) -> Either a b -> Either a c
  fmap _ (Left x)  = Left x
  fmap g (Right y) = Right (g y)

-- The ((->) a) functor as defined in GHC.Base.
instance Functor ((->) a) where
  fmap :: (b -> c) -> (a -> b) -> a -> c
  fmap = (.)

-- Or:

  -- fmap g f = \x -> g (f x)

-- A bad Maybe functor.
-- instance Functor Maybe where
--   fmap :: (a -> b) -> Maybe a -> Maybe b
--   fmap _ Nothing  = Nothing
--   fmap _ (Just _) = Nothing

-- A bad [] functor.
-- instance Functor [] where
--   fmap :: (a -> b) -> [a] -> [b]
--   fmap _ []     = []
--   fmap f (x:xs) = f x : f x : fmap f xs

-- A bad [] functor.
-- instance Functor [] where
--   fmap :: (a -> b) -> [a] -> [b]
--   fmap _ []     = []
--   fmap f (x:xs) = [f x]
