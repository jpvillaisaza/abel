------------------------------------------------------------------------------
-- Abel: A brother of Cain
--
-- The product functor
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Product.Functor where

open import Abel.Category.Functor using (Functor; mkFunctor)
open import Abel.Data.Product using (_×_; _,_)
open import Abel.Function using (id; _∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------------
-- The functor

functor : {A : Set} → Functor (_×_ A)
functor {A} = mkFunctor fmap fmap-id fmap-∘
  where
    fmap : {B C : Set} → (B → C) → A × B → A × C
    fmap g (x , y) = x , g y

    fmap-id : {B : Set} (x,y : A × B) → fmap id x,y ≡ id x,y
    fmap-id (x , y) = refl

    fmap-∘ : {B C D : Set} {g : B → C} {h : C → D}
             (x,y : A × B) → fmap (h ∘ g) x,y ≡ (fmap h ∘ fmap g) x,y
    fmap-∘ (x , y) = refl
