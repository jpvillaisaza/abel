------------------------------------------------------------------------------
-- Abel: a brother of Cain                https://github.com/jpvillaisaza/abel
--
-- Monads
------------------------------------------------------------------------------

-- (Tested with Agda 2.3.2 and the Agda standard library 0.7.)

module Abel.Category.Monad where

open import Abel.Category.Applicative
open import Abel.Category.Functor

open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------------
-- Monads

record Monad (M : Set → Set) {applicative : Applicative M} : Set₁ where
  constructor
    mkMonad

  open Applicative applicative
  open Functor functor

  infixl 1 _>>=_

  return : ∀ {A} → A → M A
  return = pure

  field
    _>>=_  : ∀ {A B} → M A → (A → M B) → M B

    return-left-id  : ∀ {A B} (x : A) (f : A → M B) → (return x >>= f) ≡ f x

    return-right-id : ∀ {A} (mx : M A) → _>>=_ {B = A} mx return ≡ mx

    >>=-assoc       : ∀ {A B C} (mx : M A) (g : B → M C) (f : A → M B) →
                      (mx >>= λ x → f x >>= g) ≡ ((mx >>= f) >>= g)

    >>=-fmap        : ∀ {A B} (f : A → B) (mx : M A) →
                      fmap f mx ≡ (mx >>= return ∘ f)

  _>>_ : ∀ {A B} → M A → M B → M B
  m >> k = m >>= λ _ → k

  join : ∀ {A} → M (M A) → M A
  join mmx = mmx >>= id
