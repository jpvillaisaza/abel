------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- The category of small types and functions
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Function.Category where

open import Abel.Data.Product using (_×_; _,_)
open import Abel.Function using (id; _∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------------
-- Associativity

associativity : {A B C D : Set} {f : A → B} {g : B → C} {h : C → D}
                (x : A) → (h ∘ g ∘ f) x ≡ ((h ∘ g) ∘ f) x
associativity _ = refl

------------------------------------------------------------------------------
-- Identity

identity : {A B : Set} {f : A → B}
           (x : A) → (id ∘ f) x ≡ f x × (f ∘ id) x ≡ f x
identity _ = refl , refl
