------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- Functors
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Category.Functor where

open import Function using (id; _∘_)

open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------------
-- Definition

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
