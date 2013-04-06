------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- The Identity monad and Kleisli triple
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Identity.Triple where

open import Abel.Category.Triple using (Triple; mkTriple)
open import Abel.Data.Identity using (Identity; identity)

open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------------
-- The Identity Kleisli triple

triple : Triple Identity
triple = mkTriple return bind associativity unity-left unity-right
  where
    return : {A : Set} → A → Identity A
    return = identity

    bind : {A B : Set} → (A → Identity B) → Identity A → Identity B
    bind f (identity x) = f x

    associativity : {A B C : Set} {f : A → Identity B} {g : B → Identity C}
                    (x : Identity A) → bind g (bind f x) ≡ bind (bind g ∘ f) x
    associativity (identity _) = refl

    unity-left : {A B : Set} {f : A → Identity B} (x : A) →
                 bind f (return x) ≡ f x
    unity-left _ = refl

    unity-right : {A : Set} (x : Identity A) → bind return x ≡ x
    unity-right (identity _) = refl
