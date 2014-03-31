------------------------------------------------------------------------------
-- Abel: A brother of Cain
--
-- The initial algebra over the N endofunctor
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Nat.Algebra where

open import Abel.Category.Algebra using (Algebra; mkAlgebra)
open import Abel.Category.Functor using (Functor; mkFunctor)
open import Abel.Data.Sum using (_+_; inj₁; inj₂; [_,_])

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤)

open import Function using (_∘_; id)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------------
-- The N endofunctor

N : Set → Set
N A = ⊤ + A

functorN : Functor N
functorN = mkFunctor fmap fmap-id fmap-∘
  where
    fmap : {A B : Set} → (A → B) → ⊤ + A → ⊤ + B
    fmap _ (inj₁ _) = inj₁ _
    fmap f (inj₂ x) = inj₂ (f x)

    fmap-id : {A : Set} (x : ⊤ + A) → fmap id x ≡ x
    fmap-id (inj₁ _) = refl
    fmap-id (inj₂ _) = refl

    fmap-∘ : {A B C : Set} {f : A → B} {g : B → C} (x : ⊤ + A) →
             fmap (g ∘ f) x ≡ fmap g (fmap f x)
    fmap-∘ (inj₁ _) = refl
    fmap-∘ (inj₂ _) = refl

------------------------------------------------------------------------------
-- The initial algebra over N

algebra : Algebra functorN
algebra = mkAlgebra ℕ [ (λ _ → zero) , suc ]
