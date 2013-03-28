------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- Monads and Kleisli triples
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Category.Triple where

open import Abel.Category.Functor

open import Function using (id; _∘_)

open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------------
-- Definition (Monad)

record Monad {M : Set → Set} (functor : Functor M) : Set₁ where

  constructor mkMonad

  open Functor functor using (fmap)

  field

    return : {A : Set} → A → M A

    join   : {A : Set} → M (M A) → M A

    assoc      : {A : Set} (mmmx : M (M (M A))) →
                 join (join mmmx) ≡ join (fmap join mmmx)

    unit-left  : {A : Set} (mx : M A) → join (return mx) ≡ mx

    unit-right : {A : Set} (mx : M A) → join (fmap return mx) ≡ mx

  bind : {A B : Set} → (A → M B) → M A → M B
  bind f = join ∘ fmap f

------------------------------------------------------------------------------
-- Definition (Kleisli triple)

record Triple (M : Set → Set) : Set₁ where

  constructor mkTriple

  field

    return : {A : Set} → A → M A

    bind   : {A B : Set} → (A → M B) → M A → M B

    assoc      : {A B C : Set} {f : A → M B} {g : B → M C} (mx : M A) →
                 bind g (bind f mx) ≡ bind (bind g ∘ f) mx

    unit-left  : {A B : Set} {f : A → M B} (x : A) → bind f (return x) ≡ f x

    unit-right : {A : Set} (mx : M A) → bind return mx ≡ mx

  infixl 1 _>>=_

  _>>=_ : {A B : Set} → M A → (A → M B) → M B
  mx >>= f = bind f mx

  fmap : {A B : Set} → (A → B) → M A → M B
  fmap f = bind (return ∘ f)

  join : ∀ {A} → M (M A) → M A
  join = bind id
