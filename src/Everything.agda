------------------------------------------------------------------------------
-- Abel: A brother of Cain
--
-- Everything
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Everything where

------------------------------------------------------------------------------
-- Category theory

import Abel.Category.Category                    -- Categories
import Abel.Category.Functor                     -- Endofunctors
import Abel.Category.NaturalTransformation       -- Natural transformations
import Abel.Category.Monad                       -- Monads and Kleisli triples

------------------------------------------------------------------------------
-- Identity

import Abel.Data.Identity

import Abel.Data.Identity.Applicative
import Abel.Data.Identity.Functor
import Abel.Data.Identity.Monad

------------------------------------------------------------------------------
-- List

import Abel.Data.List

import Abel.Data.List.Functor
import Abel.Data.List.Monad

------------------------------------------------------------------------------
-- Maybe

import Abel.Data.Maybe.Functor
import Abel.Data.Maybe.Monad

------------------------------------------------------------------------------
-- Products

import Abel.Data.Product

import Abel.Data.Product.Functor
import Abel.Data.Product.Monad

------------------------------------------------------------------------------
-- Coproducts

import Abel.Data.Sum

import Abel.Data.Sum.Functor

------------------------------------------------------------------------------
-- Function

import Abel.Function

import Abel.Function.Category
import Abel.Function.Functor
