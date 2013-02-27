------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- TODO
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Identity.Functor where

open import Abel.Category.Functor using (Functor; mkFunctor)
open import Abel.Data.Identity using (Identity; identity)

open import Function using (id; _∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------------
-- TODO

functor : Functor Identity
functor = mkFunctor fmap fmap-id fmap-∘
  where
    fmap : ∀ {A B} → (A → B) → Identity A → Identity B
    fmap f (identity x) = identity (f x)

    fmap-id : ∀ {A} (ix : Identity A) → fmap id ix ≡ id ix
    fmap-id (identity _) = refl

    fmap-∘ : ∀ {A B C} {f : A → B} {g : B → C} (ix : Identity A) →
             fmap (g ∘ f) ix ≡ (fmap g ∘ fmap f) ix
    fmap-∘ (identity _) = refl
