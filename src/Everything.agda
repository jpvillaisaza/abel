------------------------------------------------------------------------------
-- Abel: A brother of Cain
--
-- Everything
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Everything where

-- Category Theory Applied to Functional Programming in Agda

------------------------------------------------------------------------------
-- Chapter 1 (Categories)

import Abel.Function
import Abel.Function.Category

------------------------------------------------------------------------------
-- Chapter 2 (Constructions)

import Abel.Data.Empty
import Abel.Data.Unit

import Abel.Data.Product
import Abel.Data.Sum

------------------------------------------------------------------------------
-- Chapter 3 (Functors)

-- The Functor record
import Abel.Category.Functor

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
