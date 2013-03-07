------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
--
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Maybe.Monoidal where

open import Abel.Category.Functor
open import Abel.Category.Monoidal
open import Abel.Data.Maybe.Functor

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product hiding (map)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- Maybe is a monoidal functor

monoidal : Monoidal Maybe {functor}
monoidal = mkMonoidal unit _*_ nat-* left-id right-id *-assoc
  where
    open Functor functor

    unit : Maybe ⊤
    unit = just tt

    _*_ : {A B : Set} → Maybe A → Maybe B → Maybe (A × B)
    just x * just y = just (x , y)
    _      * _      = nothing

    nat-* : {A B C D : Set}
            {f : A → B} {g : C → D} (mx : Maybe A) (my : Maybe C) →
            fmap (map f g) (mx * my) ≡ fmap f mx * fmap g my
    nat-* (just _) (just _) = refl
    nat-* (just _) nothing = refl
    nat-* nothing _ = refl

    left-id  : {B : Set} (my : Maybe B) → fmap proj₂ (unit * my) ≡ my
    left-id (just _) = refl
    left-id nothing  = refl

    right-id : {A : Set} (mx : Maybe A) → fmap proj₁ (mx * unit) ≡ mx
    right-id (just _) = refl
    right-id nothing  = refl

    *-assoc : {A B C : Set} (mx : Maybe A) (my : Maybe B) (mz : Maybe C) →
              fmap assoc (mx * (my * mz)) ≡ (mx * my) * mz
    *-assoc (just _) (just _) (just _) = refl
    *-assoc (just _) (just _) nothing  = refl
    *-assoc (just _) nothing  _        = refl
    *-assoc nothing  _        _        = refl
