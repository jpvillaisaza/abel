------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- The (_⇒_ A) monad
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Function.Monad where

open import Abel.Category.Applicative
open import Abel.Category.Functor
open import Abel.Category.Monad
open import Abel.Function.Applicative

open import Function
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- (_⇒_ A) is a monad

monad : ∀ {A} → Monad (λ B → A → B) {applicative}
monad {A} = mkMonad _>>=_ return-left-id return-right-id >>=-assoc >>=-fmap
  where
    open Applicative applicative
    open Functor functor

    infixl 1 _>>=_

    return : ∀ {B} → B → A → B
    return = pure

    _>>=_ : ∀ {B C} → (A → B) → (B → A → C) → A → C
    f >>= g = λ x → g (f x) x

    return-left-id : ∀ {B C} (y : B) (g : B → A → C) → (return y >>= g) ≡ g y
    return-left-id _ _ = refl

    return-right-id : ∀ {B} (f : A → B) → (f >>= return) ≡ f
    return-right-id _ = refl

    >>=-assoc : ∀ {B C D} (f : A → B) (h : C → A → D) (g : B → A → C) →
                (f >>= λ x → g x >>= h) ≡ ((f >>= g) >>= h)
    >>=-assoc _ _ _ = refl

    >>=-fmap : ∀ {B C} (g : B → C) (f : A → B) → fmap g f ≡ (f >>= return ∘ g)
    >>=-fmap _ _ = refl
