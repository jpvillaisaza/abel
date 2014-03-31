------------------------------------------------------------------------------
-- Abel: A brother of Cain
--
-- Monoidal functors
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Category.Monoidal where

open import Abel.Category.Functor

open import Data.Product hiding (map)
open import Data.Unit using (⊤)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality as PropositionalEquality

------------------------------------------------------------------------------
-- map and assoc

map : {A B C D : Set} → (A → B) → (C → D) → A × C → B × D
map f g (x , y) = f x , g y

assoc : {A B C : Set} → A × B × C → (A × B) × C
assoc (x , y , z) = (x , y) , z

------------------------------------------------------------------------------
-- Definition

record Monoidal (F : Set → Set) {functor : Functor F} : Set₁ where
  constructor
    mkMonoidal

  open Functor functor

  field
    unit : F ⊤
    _*_  : ∀ {A B} → F A → F B → F (A × B)

    *-nat         : ∀ {A B C D}
                    {f : A → B} {h : C → D} (fx : F A) (fz : F C) →
                    fmap (map f h) (fx * fz) ≡ (fmap f fx) * (fmap h fz)

    unit-left-id  : ∀ {B} (fy : F B) → fmap proj₂ (unit * fy) ≡ fy

    unit-right-id : ∀ {A} (fx : F A) → fmap proj₁ (fx * unit) ≡ fx

    *-assoc       : ∀ {A B C} (fx : F A) (fy : F B) (fz : F C) →
                    fmap assoc (fx * (fy * fz)) ≡ (fx * fy) * fz
