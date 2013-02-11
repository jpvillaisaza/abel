------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- Categories
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Category.Category where

open import Data.Product using (_×_)

open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------------
-- Definition

record Category (_⇒_ : Set → Set → Set) : Set₁ where

  constructor mkCategory

  infixr 9 _∘_

  field

    id         : ∀ {A} → A ⇒ A

    _∘_        : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C

    ∘-assoc    : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D}
                 (x : A) → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f

    ∘-identity : ∀ {A B C} {f : A ⇒ B} {g : B ⇒ C} → id ∘ f ≡ f × g ∘ id ≡ g
