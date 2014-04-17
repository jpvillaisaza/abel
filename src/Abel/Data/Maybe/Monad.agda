------------------------------------------------------------------------------
-- Abel: A brother of Cain
--
-- The Maybe monad and Kleisli triple
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Maybe.Monad where

open import Abel.Category.Functor
open import Abel.Category.Monad
open import Abel.Data.Maybe using (Maybe; just; nothing)
open import Abel.Data.Maybe.Functor using (functor)

open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------------
-- The Maybe monad

monad' : Monad' functor
monad' = mkMonad' return join associativity unity-left unity-right
                  naturality-return naturality-join
  where
    return : {A : Set} → A → Maybe A
    return = just

    join : {A : Set} → Maybe (Maybe A) → Maybe A
    join (just mx) = mx
    join nothing   = nothing

    open Functor functor

    associativity : {A : Set} (mmmx : Maybe (Maybe (Maybe A))) →
                    join (join mmmx) ≡ join (fmap join mmmx)
    associativity (just _) = refl
    associativity nothing  = refl

    unity-left : {A : Set} (mx : Maybe A) → join (return mx) ≡ mx
    unity-left _ = refl

    unity-right : {A : Set} (mx : Maybe A) → join (fmap return mx) ≡ mx
    unity-right (just _) = refl
    unity-right nothing  = refl

    naturality-return : {A B : Set} {f : A → Maybe B} (x : A) →
                        return (f x) ≡ fmap f (return x)
    naturality-return _ = refl

    naturality-join : {A B : Set} {f : A → Maybe B} (mmx : Maybe (Maybe A)) →
                      join (fmap (fmap f) mmx) ≡ fmap f (join mmx)
    naturality-join (just _) = refl
    naturality-join nothing  = refl

------------------------------------------------------------------------------
-- The Maybe Kleisli triple

monad : Monad'' Maybe
monad = mkMonad'' return bind associativity unity-left unity-right
  where
    return : {A : Set} → A → Maybe A
    return = just

    bind : {A B : Set} → (A → Maybe B) → Maybe A → Maybe B
    bind f (just x) = f x
    bind _ nothing  = nothing

    associativity : {A B C : Set} {f : A → Maybe B} {g : B → Maybe C}
                    (mx : Maybe A) → bind g (bind f mx) ≡ bind (bind g ∘ f) mx
    associativity (just _) = refl
    associativity nothing  = refl

    unity-left : {A B : Set} {f : A → Maybe B} (x : A) →
                 bind f (return x) ≡ f x
    unity-left _ = refl

    unity-right : {A : Set} (mx : Maybe A) → bind return mx ≡ mx
    unity-right (just _) = refl
    unity-right nothing  = refl
