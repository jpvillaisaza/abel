------------------------------------------------------------------------------
-- Abel: A brother of Cain
--
-- TODO
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Function.Naturality where

open import Abel.Category.NaturalTransformation using (NT; mkNT)
open import Abel.Data.Identity using (Identity)
open import Abel.Data.Identity.Functor using (functor)
open import Abel.Function using (id; _∘_)

open import Relation.Binary.PropositionalEquality using (refl)

------------------------------------------------------------------------------
-- The id natural transformation

-- naturality-id : {A B : Set} {f : A → B} (x : Identity A) → (id ∘ fmap f) x ≡ (fmap f ∘ id) x
-- naturality-id sd = ?
--   where
--     open functor using (fmap)
