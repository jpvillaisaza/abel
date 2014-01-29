------------------------------------------------------------------------------
-- Abel: A brother of Cain
--
-- TODO
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.List.Naturality where

open import Abel.Category.Functor

open import Abel.Data.List.Functor renaming (functor to functorList)
open import Abel.Data.Maybe using (Maybe; just; nothing)
open import Abel.Data.Maybe.Functor renaming (functor to functorMaybe)

open import Data.List using (List; []; _∷_; _++_)

open import Abel.Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open Functor functorList renaming (fmap to fmapList)
open Functor functorMaybe renaming (fmap to fmapMaybe)

------------------------------------------------------------------------------
-- The head natural transformation

module Head where

  open import Abel.Data.List using (head)

  naturality : {A B : Set} {f : A → B} (xs : List A) →
               (head ∘ fmapList f) xs ≡ (fmapMaybe f ∘ head) xs
  naturality []      = refl
  naturality (_ ∷ _) = refl

------------------------------------------------------------------------------
-- The last natural transformation

module Last where

  open import Abel.Data.List using (last)

  naturality : {A B : Set} {f : A → B} (xs : List A) →
               (last ∘ fmapList f) xs ≡ (fmapMaybe f ∘ last) xs
  naturality []           = refl
  naturality (_ ∷ [])     = refl
  naturality (_ ∷ _ ∷ xs) = naturality (_ ∷ xs)
