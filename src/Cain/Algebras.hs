------------------------------------------------------------------------------
-- Category Theory Applied to Functional Programming
--
-- Chapter 7 Algebras and Initial Algebras
------------------------------------------------------------------------------

{-# LANGUAGE InstanceSigs   #-}

module Cain.Algebras where

import Prelude ()

import Cain.Categories ((.), Nat (Zero, Succ))
import Cain.Functors (Functor (fmap))

-- The foldr function as defined in GHC.Base. Actually, flip foldr.
foldr' :: b -> (a -> b -> b) -> [a] -> b
foldr' n c []     = n
foldr' n c (x:xs) = c x (foldr' n c xs)

------------------------------------------------------------------------------
-- 7.2 Algebras and Initial Algebras in Haskell

-- Example 7.2.1.

-- The N type.
data N a = Z | S a

-- The N endofunctor.
instance Functor N where
  fmap :: (a -> b) -> N a -> N b
  fmap _ Z     = Z
  fmap f (S x) = S (f x)

-- The fold function.
fold :: a -> (a -> a) -> Nat -> a
fold z s Zero     = z
fold z s (Succ n) = s (fold z s n)

-- The add function as a fold.
add :: Nat -> Nat -> Nat
add m n = fold n Succ m

-- The add function.
-- add Zero     n = n
-- add (Succ m) n = Succ (add m n)

-- The mult function as a fold.
mult :: Nat -> Nat -> Nat
mult m n = fold Zero (add n) m

-- The mult function.
-- mult Zero     n = Zero
-- mult (Succ m) n = add n (mult m n)

-- Example 7.2.2.

-- The List type.
data List a = Nil | Cons a (List a)

-- The L type.
data L a b = N | C a b

-- The (L a) functor.
instance Functor (L a) where
  fmap :: (b -> c) -> L a b -> L a c
  fmap _ N       = N
  fmap f (C x y) = C x (f y)

-- The foldr function.
foldr :: b -> (a -> b -> b) -> List a -> b
foldr n c Nil         = n
foldr n c (Cons x xs) = c x (foldr n c xs)

-- The length function as a foldr.
length :: List a -> Nat
length = foldr Zero (\_ -> Succ)

-- The lenfth function.
-- length Nil         = Zero
-- length (Cons _ xs) = Succ (length xs)

-- The append function as a foldr.
append :: List a -> List a -> List a
append xs ys = (foldr ys Cons) xs

-- The append function.
-- append Nil         ys = ys
-- append (Cons x xs) ys = Cons x (append xs ys)

-- The map function as a foldr.
map :: (a -> b) -> List a -> List b
map f = foldr Nil (Cons . f)

-- The map function.
-- map _ Nil         = Nil
-- map f (Cons x xs) = Cons (f x) (mapp f xs)
