------------------------------------------------------------------------------
-- Abel: A brother of Cain
--
-- The Maybe functor
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Maybe.Functor where

open import Abel.Category.Functor using (Functor; mkFunctor)
open import Abel.Data.Maybe using (Maybe; just; nothing)
open import Abel.Function using (id; _∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------------
-- The functor

functor : Functor Maybe
functor = mkFunctor fmap fmap-id fmap-∘
  where
    fmap : {A B : Set} → (A → B) → Maybe A → Maybe B
    fmap f (just x) = just (f x)
    fmap _ nothing  = nothing

    fmap-id : {A : Set} (mx : Maybe A) → fmap id mx ≡ id mx
    fmap-id (just _) = refl
    fmap-id nothing  = refl

    fmap-∘ : {A B C : Set} {f : A → B} {g : B → C}
             (mx : Maybe A) → fmap (g ∘ f) mx ≡ (fmap g ∘ fmap f) mx
    fmap-∘ (just _) = refl
    fmap-∘ nothing  = refl
