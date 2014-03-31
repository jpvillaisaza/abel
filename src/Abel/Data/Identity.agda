------------------------------------------------------------------------------
-- Abel: A brother of Cain
--
-- The Identity type
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Identity where

------------------------------------------------------------------------------
-- The Identity type

data Identity (A : Set) : Set where
  identity : (x : A) → Identity A
