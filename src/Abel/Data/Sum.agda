------------------------------------------------------------------------------
-- Abel: A brother of Cain
--
-- Coproducts
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Sum where

------------------------------------------------------------------------------
-- The _+_ (coproduct) type

infixr 1 _+_

data _+_ (A B : Set) : Set where
  inj₁ : (x : A) → A + B
  inj₂ : (y : B) → A + B

[_,_] : {A B C : Set} (f : A → C) (g : B → C) → A + B → C
[_,_] f _ (inj₁ x) = f x
[_,_] _ g (inj₂ y) = g y
