------------------------------------------------------------------------------
-- Abel: a brother of Cain                https://github.com/jpvillaisaza/abel
--
-- (_×_ A) is a functor
------------------------------------------------------------------------------

module Abel.Data.Product.Functor where

open import Abel.Category.Functor using (Functor; mkFunctor)

open import Data.Product using (_×_; _,_)

open import Relation.Binary.PropositionalEquality using (refl)

functor : ∀ {A} → Functor (_×_ A)
functor {A} = mkFunctor fmap (λ _ → refl) (λ _ → refl)
  where
    fmap : ∀ {B C} → (B → C) → A × B → A × C
    fmap f (x , y) = x , f y
