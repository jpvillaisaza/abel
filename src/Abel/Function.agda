------------------------------------------------------------------------------
-- Abel: A brother of Cain
--
-- Functions
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Function where

open import Relation.Binary.PropositionalEquality using (refl)

infixr 9 _∘_

------------------------------------------------------------------------------
-- Identity function

id : {A : Set} → A → A
id x = x

------------------------------------------------------------------------------
-- Function composition

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
g ∘ f = λ x → g (f x)
