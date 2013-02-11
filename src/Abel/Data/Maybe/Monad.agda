------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- The Maybe monad
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Maybe.Monad where

open import Abel.Category.Applicative
open import Abel.Category.Functor
open import Abel.Category.Monad
open import Abel.Data.Maybe.Applicative

open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------------
-- Maybe is a monad

monad : Monad Maybe {applicative}
monad = mkMonad _>>=_ return-left-id return-right-id >>=-assoc >>=-fmap
  where
    open Applicative applicative
    open Functor functor

    infixl 1 _>>=_

    return : ∀ {A} → A → Maybe A
    return = pure

    _>>=_ : ∀ {A B} → Maybe A → (A → Maybe B) → Maybe B
    just x  >>= f = f x
    nothing >>= _ = nothing

    return-left-id : ∀ {A B} (x : A) (f : A → Maybe B) →
                     (return x >>= f) ≡ f x
    return-left-id _ _ = refl

    return-right-id : ∀ {A} (mx : Maybe A) → (mx >>= return) ≡ mx
    return-right-id (just _) = refl
    return-right-id nothing  = refl

    >>=-assoc : ∀ {A B C} (mx : Maybe A) (g : B → Maybe C) (f : A → Maybe B) →
                (mx >>= λ x → f x >>= g) ≡ ((mx >>= f) >>= g)
    >>=-assoc (just _) _ _ = refl
    >>=-assoc nothing  _ _ = refl

    >>=-fmap : ∀ {A B} (f : A → B) (mx : Maybe A) →
               fmap f mx ≡ (mx >>= return ∘ f)
    >>=-fmap _ (just _) = refl
    >>=-fmap _ nothing  = refl
