------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- The Maybe monad and Kleisli triple
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Maybe.Triple where

open import Abel.Category.Functor
open import Abel.Category.Triple using (Monad; mkMonad; Triple; mkTriple)
open import Abel.Data.Maybe.Functor using (functor)

open import Data.Maybe using (Maybe; just; nothing)

open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------------
-- The Maybe monad

monad : Monad functor
monad = mkMonad return join assoc unit-left unit-right
  where
    return : {A : Set} → A → Maybe A
    return = just

    join : {A : Set} → Maybe (Maybe A) → Maybe A
    join (just mx) = mx
    join nothing   = nothing

    open Functor functor

    assoc : {A : Set} (mmmx : Maybe (Maybe (Maybe A))) →
            join (join mmmx) ≡ join (fmap join mmmx)
    assoc (just _) = refl
    assoc nothing  = refl

    unit-left : {A : Set} (mx : Maybe A) → join (return mx) ≡ mx
    unit-left _ = refl

    unit-right : {A : Set} (mx : Maybe A) → join (fmap return mx) ≡ mx
    unit-right (just _) = refl
    unit-right nothing  = refl

------------------------------------------------------------------------------
-- The Maybe Kleisli triple

triple : Triple Maybe
triple = mkTriple return bind assoc unit-left unit-right
  where
    return : {A : Set} → A → Maybe A
    return = just

    bind : {A B : Set} → (A → Maybe B) → Maybe A → Maybe B
    bind f (just x) = f x
    bind _ nothing  = nothing

    assoc : {A B C : Set} {f : A → Maybe B} {g : B → Maybe C} (mx : Maybe A) →
            bind g (bind f mx) ≡ bind (bind g ∘ f) mx
    assoc (just _) = refl
    assoc nothing  = refl

    unit-left : {A B : Set} {f : A → Maybe B} (x : A) →
                bind f (return x) ≡ f x
    unit-left _ = refl

    unit-right : {A : Set} (mx : Maybe A) → bind return mx ≡ mx
    unit-right (just _) = refl
    unit-right nothing  = refl
