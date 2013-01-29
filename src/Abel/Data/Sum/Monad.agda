------------------------------------------------------------------------------
-- Abel: a brother of Cain                https://github.com/jpvillaisaza/abel
--
-- The (_⊎_ A) monad
------------------------------------------------------------------------------

-- (Tested with Agda 2.3.2 and the Agda standard library 0.7.)

module Abel.Data.Sum.Monad where

open import Abel.Category.Applicative
open import Abel.Category.Functor
open import Abel.Category.Monad
open import Abel.Data.Sum.Applicative

open import Data.Sum
open import Function
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- (_⊎_ A) is a monad

monad : ∀ {A} → Monad (_⊎_ A) {applicative}
monad {A} = mkMonad _>>=_ return-left-id return-right-id >>=-assoc >>=-fmap
  where
    open Applicative applicative
    open Functor functor

    infixl 1 _>>=_

    return : ∀ {B} → B → A ⊎ B
    return = pure

    _>>=_ : ∀ {B C} → A ⊎ B → (B → A ⊎ C) → A ⊎ C
    inj₁ x >>= _ = inj₁ x
    inj₂ y >>= g = g y

    return-left-id : ∀ {B C} (y : B) (g : B → A ⊎ C) → (return y >>= g) ≡ g y
    return-left-id _ _ = refl

    return-right-id : ∀ {B} (x⊎y : A ⊎ B) → (x⊎y >>= return) ≡ x⊎y
    return-right-id (inj₁ _) = refl
    return-right-id (inj₂ _) = refl

    >>=-assoc : ∀ {B C D} (x⊎y : A ⊎ B) (h : C → A ⊎ D) (g : B → A ⊎ C) →
                (x⊎y >>= λ x → g x >>= h) ≡ (x⊎y >>= g >>= h)
    >>=-assoc (inj₁ _) _ _ = refl
    >>=-assoc (inj₂ _) _ _ = refl

    >>=-fmap : ∀ {B C} (g : B → C) (x,y : A ⊎ B) →
               fmap g x,y ≡ (x,y >>= return ∘ g)
    >>=-fmap _ (inj₁ _) = refl
    >>=-fmap _ (inj₂ _) = refl
