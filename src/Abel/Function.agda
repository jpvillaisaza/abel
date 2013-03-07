------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- Functions
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Function where

open import Abel.Category.NaturalTransformation using (NT; mkNT)
open import Abel.Data.Identity.Functor renaming (functor to functorId)

open import Function using (id)

open import Relation.Binary.PropositionalEquality using (refl)

------------------------------------------------------------------------------
-- The id natural transformation

idNT : NT functorId functorId
idNT = mkNT id (λ _ → refl)
