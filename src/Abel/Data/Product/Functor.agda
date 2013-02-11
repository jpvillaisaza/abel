------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- TODO
------------------------------------------------------------------------------

module Abel.Data.Product.Functor where

open import Abel.Category.Functor using (Functor; mkFunctor)

open import Data.Product using (_×_; _,_)

open import Relation.Binary.PropositionalEquality using (refl)

------------------------------------------------------------------------------
-- TODO

functor : ∀ {A} → Functor (_×_ A)
functor {A} = mkFunctor fmap (λ _ → refl) (λ _ → refl)
  where
    fmap : ∀ {B C} → (B → C) → A × B → A × C
    fmap g (x , y) = x , g y
