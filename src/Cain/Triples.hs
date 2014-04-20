------------------------------------------------------------------------------
-- Category Theory Applied to Functional Programming
--
-- Chapter 6 Monads and Kleisli Triples
------------------------------------------------------------------------------

{-# LANGUAGE InstanceSigs   #-}

module Cain.Triples where

import Prelude ()

import Cain.Categories (id, (.))
import Cain.Functors (Identity (Identity), map, Maybe (Nothing, Just))
import Cain.Naturals (concat)

infixl 1 >>=
infixr 1 =<<

------------------------------------------------------------------------------
-- 6.2.2 Kleisli Triples in Haskell

-- The Kleisli triple type class
class Monad'' m where
  return :: a -> m a
  bind   :: (a -> m b) -> m a -> m b

-- The (>>=) function.
(>>=) :: Monad'' m => m a -> (a -> m b) -> m b
mx >>= f = bind f mx

-- The (=<<) function (see Control.Monad).
(=<<) :: Monad'' m => (a -> m b) -> m a -> m b
(=<<) = bind

-- The Identity Kleisli triple.
instance Monad'' Identity where
  return :: a -> Identity a
  return = Identity

  bind :: (a -> Identity b) -> Identity a -> Identity b
  bind f (Identity x) = f x

-- The Maybe Kleisli triple (see Data.Maybe).
instance Monad'' Maybe where
  return :: a -> Maybe a
  return = Just

  bind :: (a -> Maybe b) -> Maybe a -> Maybe b
  bind _ Nothing  = Nothing
  bind f (Just x) = f x

-- The [] Kleisli triple (see GHC.Base).
instance Monad'' [] where
  return :: a -> [a]
  return x = [x]

  bind :: (a -> [b]) -> [a] -> [b]
  bind f xs = concat (map f xs)

------------------------------------------------------------------------------
-- 6.2.3 Equivalence of Monads and Kleisli Triples in Haskell

-- The fmap function.
fmap :: Monad'' m => (a -> b) -> m a -> m b
fmap f mx = bind (return . f) mx

-- The liftM function as defined in Control.Monad.
liftM :: Monad'' m => (a -> b) -> m a -> m b
liftM f mx = mx >>= (return . f)

-- The join function.
join :: Monad'' m => m (m a) -> m a
join mmx = bind id mmx

-- Or, as defined in Control.Monad:

-- join mmx = mmx >>= id
