------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- TODO
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Identity.Monad where

open import Abel.Category.Applicative
open import Abel.Category.Functor
open import Abel.Category.Monad
open import Abel.Data.Identity
open import Abel.Data.Identity.Applicative using (applicative)

open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------------
-- TODO

monad : Monad Identity {applicative}
monad = mkMonad _>>=_ (λ _ _ → refl) return-right-id >>=-assoc >>=-fmap
  where
    infixl 1 _>>=_

    _>>=_ : ∀ {A B} → Identity A → (A → Identity B) → Identity B
    identity x >>= f = f x

    open Applicative applicative using (pure; functor)

    return-right-id : ∀ {A} (ix : Identity A) → _>>=_ {B = A} ix pure ≡ ix
    return-right-id (identity _) = refl

    >>=-assoc : ∀ {A B C} (ix : Identity A)
                (g : B → Identity C) (f : A → Identity B) →
                (ix >>= λ x → f x >>= g) ≡ ((ix >>= f) >>= g)
    >>=-assoc (identity _) _ _ = refl

    open Functor functor

    >>=-fmap : ∀ {A B} (f : A → B) (ix : Identity A) →
               fmap f ix ≡ (ix >>= pure ∘ f)
    >>=-fmap _ (identity _) = refl
