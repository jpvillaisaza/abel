------------------------------------------------------------------------------
-- Abel: A brother of Cain
--
-- Functors
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Category.Functor where

open import Abel.Function using (id; _∘_)

open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------------
-- Definition

record Functor (F : Set → Set) : Set₁ where

  constructor mkFunctor

  field

    fmap    : {A B : Set} → (A → B) → F A → F B

    fmap-id : {A : Set} (fx : F A) → fmap id fx ≡ id fx

    fmap-∘  : {A B C : Set} {f : A → B} {g : B → C}
              (fx : F A) → fmap (g ∘ f) fx ≡ (fmap g ∘ fmap f) fx

  infixl 4 _<$>_

  _<$>_ : ∀ {A B} → (A → B) → F A → F B
  _<$>_ = fmap
