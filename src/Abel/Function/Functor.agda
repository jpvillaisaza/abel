------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- TODO
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Function.Functor where

open import Abel.Category.Functor using (Functor; mkFunctor)

open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (refl)

------------------------------------------------------------------------------
-- TODO

functor : ∀ {A} → Functor (λ B → A → B)
functor {A} = mkFunctor (λ g f → g ∘ f) (λ _ → refl) (λ _ → refl)
