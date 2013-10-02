------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- Categories
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Category.Category where

open import Abel.Data.Product using (_×_)

open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------------
-- Definition

record Category (_⇒_ : Set → Set → Set) : Set₁ where

  constructor mkCategory

  infixr 9 _∘_

  field

    id            : {A : Set} → A ⇒ A

    _∘_           : {A B C : Set} → B ⇒ C → A ⇒ B → A ⇒ C

    associativity : {A B C D : Set} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D}
                    (x : A) → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f

    identity      : {A B : Set} {f : A ⇒ B} → id ∘ f ≡ f × f ∘ id ≡ f
