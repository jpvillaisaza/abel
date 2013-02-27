------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- Natural transformations
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Category.NaturalTransformation where

open import Abel.Category.Functor

open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------------
-- Definition

record NaturalTransformation {F G : Set → Set}
                             (functorF : Functor F)
                             (functorG : Functor G) : Set₁ where

  constructor mkNT

  open Functor functorF renaming (fmap to fmapF)
  open Functor functorG renaming (fmap to fmapG)

  field

    τ          : ∀ {A} → F A → G A

    naturality : ∀ {A B} {f : A → B}
                 (fx : F A) → (τ ∘ fmapF f) fx ≡ (fmapG f ∘ τ) fx
