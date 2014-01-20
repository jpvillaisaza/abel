------------------------------------------------------------------------------
-- Abel: A brother of Cain
--
-- The Maybe functor
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Maybe where

------------------------------------------------------------------------------
-- The type

data Maybe (A : Set) : Set where
  just    : (x : A) → Maybe A
  nothing : Maybe A
