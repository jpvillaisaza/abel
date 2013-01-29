------------------------------------------------------------------------------
-- Abel: a brother of Cain                https://github.com/jpvillaisaza/abel
--
-- Functors
------------------------------------------------------------------------------

-- (Tested with Agda 2.3.2 and the Agda standard library 0.7.)

module Abel.Category.Functor where

open import Function using (id; _∘_)

open import Relation.Binary.PropositionalEquality using (_≡_)

record Functor (F : Set → Set) : Set₁ where

  constructor mkFunctor

  field

    fmap    : ∀ {A B} → (A → B) → F A → F B

    fmap-id : ∀ {A} (Fx : F A) → fmap id Fx ≡ id Fx

    fmap-∘  : ∀ {A B C} {f : A → B} {g : B → C}
              (Fx : F A) → fmap (g ∘ f) Fx ≡ (fmap g ∘ fmap f) Fx

  infixl 4 _<$>_

  _<$>_ : ∀ {A B} → (A → B) → F A → F B
  _<$>_ = fmap
