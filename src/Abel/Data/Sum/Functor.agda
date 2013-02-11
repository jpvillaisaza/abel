------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- TODO
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Sum.Functor where

open import Abel.Category.Functor using (Functor; mkFunctor)

open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Function using (id; _∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------------
-- TODO

functor : ∀ {A} → Functor (_⊎_ A)
functor {A} = mkFunctor fmap fmap-id fmap-∘
  where
    fmap : ∀ {B C} → (B → C) → A ⊎ B → A ⊎ C
    fmap _ (inj₁ x) = inj₁ x
    fmap g (inj₂ y) = inj₂ (g y)

    fmap-id : ∀ {B} (x⊎y : A ⊎ B) → fmap id x⊎y ≡ id x⊎y
    fmap-id (inj₁ _) = refl
    fmap-id (inj₂ _) = refl

    fmap-∘ : ∀ {B C D} {g : B → C} {h : C → D}
             (x⊎y : A ⊎ B) → fmap (h ∘ g) x⊎y ≡ (fmap h ∘ fmap g) x⊎y
    fmap-∘ (inj₁ _) = refl
    fmap-∘ (inj₂ _) = refl
