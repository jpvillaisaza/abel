------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- Lists
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
-- The head natural transformation

headNT : NaturalTransformation functorList functorMaybe
headNT = mkNT head naturality
  where
    open Functor functorList renaming (fmap to fmapList)
    open Functor functorMaybe renaming (fmap to fmapMaybe)

    naturality : {A B : Set} {f : A → B} (xs : List A) →
                 (head ∘ fmapList f) xs ≡ (fmapMaybe f ∘ head) xs
    naturality []      = refl
    naturality (_ ∷ _) = refl

------------------------------------------------------------------------------
-- TODO

last : {A : Set} → List A → Maybe A
last []       = nothing
last (x ∷ []) = just x
last (_ ∷ xs) = last xs

------------------------------------------------------------------------------
-- The last natural transformation

lastNT : NaturalTransformation functorList functorMaybe
lastNT = mkNT last naturality
  where
    open Functor functorList renaming (fmap to fmapList)
    open Functor functorMaybe renaming (fmap to fmapMaybe)

    naturality : {A B : Set} {f : A → B} (xs : List A) →
                 (last ∘ fmapList f) xs ≡ (fmapMaybe f ∘ last) xs
    naturality []           = refl
    naturality (_ ∷ [])     = refl
    naturality (_ ∷ _ ∷ xs) = naturality (_ ∷ xs)
