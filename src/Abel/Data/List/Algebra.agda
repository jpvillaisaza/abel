------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- TODO
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.List.Algebra where

open import Abel.Category.Algebra using (Algebra; mkAlgebra)
open import Abel.Category.Functor using (Functor; mkFunctor)
open import Abel.Data.List.Functor renaming (functor to functorList)
open import Abel.Data.Product using (_×_; _,_; uncurry)
open import Abel.Data.Sum using (_+_; inj₁; inj₂; [_,_])

open import Data.Unit using (⊤)

open import Function using (_∘_; id)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------------
-- TODO

infixr 5 _∷_

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

------------------------------------------------------------------------------
-- TODO

L : {A : Set} → Set → Set
L {A} B = ⊤ + A × B

functorL : {A : Set} → Functor L
functorL {A} = mkFunctor fmap fmap-id fmap-∘
  where
    fmap : {B C : Set} → (B → C) → ⊤ + A × B → ⊤ + A × C
    fmap _ (inj₁ _)       = inj₁ _
    fmap g (inj₂ (x , y)) = inj₂ (x , (g y))

    fmap-id : {B : Set} (x : ⊤ + A × B) → fmap id x ≡ x
    fmap-id (inj₁ _)       = refl
    fmap-id (inj₂ (_ , _)) = refl

    fmap-∘ : {B C D : Set} {f : B → C} {g : C → D} (x : ⊤ + A × B) →
             fmap (g ∘ f) x ≡ fmap g (fmap f x)
    fmap-∘ (inj₁ _)       = refl
    fmap-∘ (inj₂ (_ , _)) = refl

------------------------------------------------------------------------------
-- TODO

algebra : {A : Set} → Algebra functorL
algebra {A} = mkAlgebra (List A) [ (λ _ → []) , uncurry _∷_ ]
