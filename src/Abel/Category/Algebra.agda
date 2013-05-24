------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- Algebras (over endofunctors)
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Category.Algebra where

open import Abel.Category.Functor using (Functor)

------------------------------------------------------------------------------
-- Definition

record Algebra {F : Set → Set} (functorF : Functor F) : Set₁ where

  constructor mkAlgebra

  field

    A : Set

    α : F A → A
