------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- The Identity monad and Kleisli triple
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Identity.Triple where

open import Abel.Category.Functor
open import Abel.Category.Triple using (Monad; mkMonad; Triple; mkTriple)
open import Abel.Data.Identity using (Identity; identity)
open import Abel.Data.Identity.Functor using (functor)

open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------------
-- The Identity monad

monad : Monad functor
monad = mkMonad return join associativity unit-left unit-right
  where
    return : {A : Set} → A → Identity A
    return = identity

    join : {A : Set} → Identity (Identity A) → Identity A
    join (identity x) = x

    open Functor functor

    associativity : {A : Set} (iiix : Identity (Identity (Identity A))) →
                    join (join iiix) ≡ join (fmap join iiix)
    associativity (identity _) = refl

    unit-left : {A : Set} (ix : Identity A) → join (return ix) ≡ ix
    unit-left (identity _) = refl

    unit-right : {A : Set} (ix : Identity A) → join (fmap return ix) ≡ ix
    unit-right (identity _) = refl

------------------------------------------------------------------------------
-- The Identity Kleisli triple

triple : Triple Identity
triple = mkTriple return bind unity₁ unity₂ associativity
  where
    return : {A : Set} → A → Identity A
    return = identity

    bind : {A B : Set} → (A → Identity B) → Identity A → Identity B
    bind f (identity x) = f x

    unity₁ : {A : Set} (ix : Identity A) → bind return ix ≡ ix
    unity₁ (identity _) = refl

    unity₂ : {A B : Set} {f : A → Identity B} (x : A) → bind f (return x) ≡ f x
    unity₂ _ = refl

    associativity : {A B C : Set} {f : A → Identity B} {g : B → Identity C}
                    (ix : Identity A) →
                    bind g (bind f ix) ≡ bind (bind g ∘ f) ix
    associativity (identity _) = refl
