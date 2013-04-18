------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- TODO
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Identity.Monad where

open import Abel.Category.Functor
open import Abel.Category.Monad
open import Abel.Data.Identity using (Identity; identity)
open import Abel.Data.Identity.Functor using (functor)

open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------------
-- TODO

monad' : Monad' functor
monad' = mkMonad' return join associativity unity-left unity-right
                  naturality-return naturality-join
  where
    return : {A : Set} → A → Identity A
    return = identity

    join : {A : Set} → Identity (Identity A) → Identity A
    join (identity x) = x

    open Functor functor using (fmap)

    associativity : {A : Set} (x : Identity (Identity (Identity A))) →
                    join (join x) ≡ join (fmap join x)
    associativity (identity _) = refl

    unity-left : {A : Set} (x : Identity A) → join (return x) ≡ x
    unity-left _ = refl

    unity-right : {A : Set} (x : Identity A) → join (fmap return x) ≡ x
    unity-right (identity _) = refl

    naturality-return : {A B : Set} {f : A → Identity B} (x : A) →
                        return (f x) ≡ fmap f (return x)
    naturality-return _ = refl

    naturality-join : {A B : Set} {f : A → Identity B}
                      (x : Identity (Identity A)) →
                      join (fmap (fmap f) x) ≡ fmap f (join x)
    naturality-join (identity _) = refl

------------------------------------------------------------------------------
-- TODO

monad : Monad Identity
monad = mkMonad return bind associativity unity-left unity-right
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
