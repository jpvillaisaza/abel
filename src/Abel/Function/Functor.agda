------------------------------------------------------------------------------
-- Abel: A brother of Cain
--
-- The function functor
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Function.Functor where

open import Abel.Category.Functor using (Functor; mkFunctor)
open import Abel.Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (refl)

------------------------------------------------------------------------------
-- The functor

functor : {A : Set} → Functor (λ B → A → B)
functor = mkFunctor (λ g f → g ∘ f) (λ _ → refl) (λ _ → refl)
