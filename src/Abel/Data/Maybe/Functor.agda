------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- TODO
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Maybe.Functor where

open import Abel.Category.Functor using (Functor; mkFunctor)

open import Data.Maybe using (Maybe; just; nothing)

open import Function using (id; _∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------------
-- TODO

functor : Functor Maybe
functor = mkFunctor fmap fmap-id fmap-∘
  where
    fmap : ∀ {A B} → (A → B) → Maybe A → Maybe B
    fmap f (just x) = just (f x)
    fmap _ nothing  = nothing

    fmap-id : ∀ {A} (Mx : Maybe A) → fmap id Mx ≡ id Mx
    fmap-id (just _) = refl
    fmap-id nothing  = refl

    fmap-∘ : ∀ {A B C} {f : A → B} {g : B → C}
             (Mx : Maybe A) → fmap (g ∘ f) Mx ≡ (fmap g ∘ fmap f) Mx
    fmap-∘ (just _) = refl
    fmap-∘ nothing  = refl
