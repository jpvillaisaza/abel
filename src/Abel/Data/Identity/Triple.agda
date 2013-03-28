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
monad = mkMonad return join assoc unit-left unit-right
  where
    return : {A : Set} → A → Identity A
    return = identity

    join : {A : Set} → Identity (Identity A) → Identity A
    join (identity x) = x

    open Functor functor

    assoc : {A : Set} (iiix : Identity (Identity (Identity A))) →
            join (join iiix) ≡ join (fmap join iiix)
    assoc (identity _) = refl

    unit-left : {A : Set} (ix : Identity A) → join (return ix) ≡ ix
    unit-left (identity _) = refl

    unit-right : {A : Set} (ix : Identity A) → join (fmap return ix) ≡ ix
    unit-right (identity _) = refl

------------------------------------------------------------------------------
-- The Identity Kleisli triple

triple : Triple Identity
triple = mkTriple return bind assoc unit-left unit-right
  where
    return : {A : Set} → A → Identity A
    return = identity

    bind : {A B : Set} → (A → Identity B) → Identity A → Identity B
    bind f (identity x) = f x

    unit-right : {A : Set} (ix : Identity A) → bind return ix ≡ ix
    unit-right (identity _) = refl

    unit-left : {A B : Set} {f : A → Identity B} (x : A) →
                bind f (return x) ≡ f x
    unit-left _ = refl

    assoc : {A B C : Set} {f : A → Identity B} {g : B → Identity C}
            (ix : Identity A) → bind g (bind f ix) ≡ bind (bind g ∘ f) ix
    assoc (identity _) = refl
