------------------------------------------------------------------------------
-- Category Theory Applied to Functional Programming
--
-- Chapter 6 Monads and Kleisli Triples
------------------------------------------------------------------------------

{-# LANGUAGE InstanceSigs   #-}

module Cain.Monads where

import Prelude ()

import Cain.Functors(Functor (fmap),
                     Identity (Identity),
                     Maybe (Nothing, Just))
import Cain.Naturals (concat)

infixl 1 >>=

-- The Cartesian product.
cartesian :: [a] -> [b] -> [(a,b)]
cartesian xs ys = [(x,y) | x <- xs, y <- ys]

-- Or:

-- cartesian xs ys = xs >>= \x -> ys >>= \y -> return (x,y)

------------------------------------------------------------------------------
-- 6.2.1 Monads in Haskell

-- The Monad' type class.
class Functor m => Monad' m where
  return :: a -> m a
  join   :: m (m a) -> m a

-- The Identity monad.
instance Monad' Identity where
  return :: a -> Identity a
  return = Identity

  join :: Identity (Identity a) -> Identity a
  join (Identity mx) = mx

-- The Maybe monad.
instance Monad' Maybe where
  return :: a -> Maybe a
  return = Just

  join :: Maybe (Maybe a) -> Maybe a
  join Nothing   = Nothing
  join (Just mx) = mx

-- The [] monad.
instance Monad' [] where
  return :: a -> [a]
  return x = [x]

  join :: [[a]] -> [a]
  join = concat

------------------------------------------------------------------------------
-- 6.2.3 Equivalence of Monads and Kleisli Triples in Haskell

-- The bind function.
bind :: Monad' m => (a -> m b) -> m a -> m b
bind f mx = join (fmap f mx)

-- The (>>=) function.
(>>=) :: Monad' m => m a -> (a -> m b) -> m b
mx >>= f = join (fmap f mx)
