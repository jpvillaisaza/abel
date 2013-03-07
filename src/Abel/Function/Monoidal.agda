------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- TODO
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Function.Monoidal where

open import Abel.Category.Functor
open import Abel.Category.Monoidal
open import Abel.Function
open import Abel.Function.Functor

open import Data.Product hiding (map)
open import Data.Unit using (⊤)
open import Function
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- TODO

monoidal : ∀ {A} → Monoidal (λ B → A → B) {functor}
monoidal {A} = mkMonoidal unit _*_
                          (λ _ _ → refl) unit-left-id unit-right-id *-assoc
  where
    open Functor functor

    unit : A → ⊤
    unit _ = _

    _*_ : ∀ {B C} → (A → B) → (A → C) → A → B × C
    f * g = λ x → f x , g x

    *-nat : ∀ {B C D E : Set} {g : B → C} {i : D → E} (f : A → B) (h : A → D) →
            fmap (map g i) (f * h) ≡ (fmap g f) * (fmap i h)
    *-nat _ _ = refl

    unit-left-id : ∀ {C} (g : A → C) → fmap proj₂ (unit * g) ≡ g
    unit-left-id _ = refl

    unit-right-id : ∀ {B} (f : A → B) → fmap proj₁ (f * unit) ≡ f
    unit-right-id _ = refl

    *-assoc : ∀ {B C D} (f : A → B) (g : A → C) (h : A → D) →
              fmap assoc (f * (g * h)) ≡ (f * g) * h
    *-assoc _ _ _ = refl
