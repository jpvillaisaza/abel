------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- TODO
------------------------------------------------------------------------------

module Abel.Function.Functor where

open import Abel.Category.Functor using (Functor; mkFunctor)
open import Abel.Function using (_⇒_)

open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (refl)

------------------------------------------------------------------------------
-- TODO

functor : ∀ {A} → Functor (_⇒_ A)
functor {A} = mkFunctor fmap (λ _ → refl) (λ _ → refl)
  where
    fmap : ∀ {B C} → (B → C) → A ⇒ B → A ⇒ C
    fmap g f = g ∘ f
