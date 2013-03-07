------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
--
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Sum.Monoidal where

open import Abel.Category.Functor
open import Abel.Category.Monoidal
open import Abel.Data.Sum.Functor

open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- (_⊎_ A) is a monoidal functor

monoidal : ∀ {A} → Monoidal (_⊎_ A) {functor}
monoidal {A} = mkMonoidal unit _*_ nat-* left-id right-id associa
  where
    open Functor functor

    unit : A ⊎ ⊤
    unit = inj₂ tt

    _*_ : ∀ {B C} → A ⊎ B → A ⊎ C → A ⊎ B × C
    inj₁ x * _   = inj₁ x
    inj₂ y * x,z = fmap (_,_ y) x,z

    nat-* : ∀ {B C D E}
            {g : B → C} {i : D → E} (x⊎y : A ⊎ B) (x⊎w : A ⊎ D) →
            fmap (map g i) (x⊎y * x⊎w) ≡ fmap g x⊎y * fmap i x⊎w
    nat-* (inj₁ _) _        = refl
    nat-* (inj₂ _) (inj₁ _) = refl
    nat-* (inj₂ _) (inj₂ _) = refl

    left-id : ∀ {C} (x⊎z : A ⊎ C) → fmap proj₂ (unit * x⊎z) ≡ x⊎z
    left-id (inj₁ _) = refl
    left-id (inj₂ _) = refl

    right-id : ∀ {B} (x⊎y : A ⊎ B) → fmap proj₁ (x⊎y * unit) ≡ x⊎y
    right-id (inj₁ _) = refl
    right-id (inj₂ _) = refl

    associa : ∀ {B C D} (x⊎y : A ⊎ B) (x⊎z : A ⊎ C) (x⊎w : A ⊎ D) →
              fmap assoc (x⊎y * (x⊎z * x⊎w)) ≡ (x⊎y * x⊎z) * x⊎w
    associa (inj₁ _) _        _        = refl
    associa (inj₂ _) (inj₁ _) _        = refl
    associa (inj₂ _) (inj₂ _) (inj₁ _) = refl
    associa (inj₂ _) (inj₂ _) (inj₂ _) = refl
