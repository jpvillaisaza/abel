------------------------------------------------------------------------------
-- Abel: A brother of Cain
--
-- The Identity endofunctor
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Identity.Functor where

open import Abel.Category.Functor using (Functor; mkFunctor)
open import Abel.Data.Identity using (Identity; identity)

open import Function using (id; _∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------------
-- The functor

functor : Functor Identity
functor = mkFunctor fmap fmap-id fmap-∘
  where
    fmap : ∀ {A B} → (A → B) → Identity A → Identity B
    fmap f (identity x) = identity (f x)

    fmap-id : ∀ {A} (x : Identity A) → fmap id x ≡ id x
    fmap-id (identity _) = refl

    fmap-∘ : ∀ {A B C} {f : A → B} {g : B → C} (x : Identity A) →
             fmap (g ∘ f) x ≡ (fmap g ∘ fmap f) x
    fmap-∘ (identity _) = refl
