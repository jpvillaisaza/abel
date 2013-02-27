------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- TODO
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.List where

open import Abel.Category.Functor
open import Abel.Category.NaturalTransformation using (NaturalTransformation; mkNT)
open import Abel.Data.List.Functor renaming (functor to functorList)
open import Abel.Data.Maybe.Functor renaming (functor to functorMaybe)

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)

open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------------
-- TODO

head : {A : Set} → List A → Maybe A
head []      = nothing
head (x ∷ _) = just x

------------------------------------------------------------------------------
-- TODO

headNT : NaturalTransformation functorList functorMaybe
headNT = mkNT head naturality
  where
    open Functor functorList renaming (fmap to fmapList)
    open Functor functorMaybe renaming (fmap to fmapMaybe)

    naturality : ∀ {A B} {f : A → B} (xs : List A) →
                 (head ∘ fmapList f) xs ≡ (fmapMaybe f ∘ head) xs
    naturality []      = refl
    naturality (_ ∷ _) = refl
