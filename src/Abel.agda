------------------------------------------------------------------------------
-- Category Theory Applied to Functional Programming
--
-- Agda code
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel where

-- (Tested with Agda 2.3.2.2 and the Agda standard library 0.7.)

------------------------------------------------------------------------------
-- Chapter 1 (Categories)

-- Identity and composition
import Abel.Function

-- Associativity and identity
import Abel.Function.Category

------------------------------------------------------------------------------
-- Chapter 2 (Constructions)

-- The empty and unit types
import Abel.Data.Empty
import Abel.Data.Unit

-- Products and coproducts
import Abel.Data.Product
import Abel.Data.Sum

------------------------------------------------------------------------------
-- Chapter 3 (Functors)

-- The Functor record
import Abel.Category.Functor

-- The Identity, Maybe, and List types
import Abel.Data.Identity
import Abel.Data.Maybe
import Abel.Data.List

-- The Identity, Functor, and List functors
import Abel.Data.Identity.Functor
import Abel.Data.Maybe.Functor
import Abel.Data.List.Functor

-- The Product and Sum functors
import Abel.Data.Product.Functor
import Abel.Data.Sum.Functor

-- The Function functor
import Abel.Function.Functor

------------------------------------------------------------------------------
-- Chapter 5 (Monads and Kleisli triples)

-- The Monad and Monad' records
import Abel.Category.Monad

-- The Identity, Maybe, and List monads and Kleisli triples
import Abel.Data.Identity.Monad
import Abel.Data.Maybe.Monad
import Abel.Data.List.Monad
