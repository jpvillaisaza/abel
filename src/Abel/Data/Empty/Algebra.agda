------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- TODO
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Empty.Algebra where

open import Abel.Category.Algebra using (Algebra; mkAlgebra)
open import Abel.Data.Identity using (Identity; identity)
open import Abel.Data.Identity.Functor renaming (functor to functorI)

open import Data.Empty using (⊥)

------------------------------------------------------------------------------
-- TODO

algebra : Algebra functorI
algebra = mkAlgebra ⊥ α
  where
    α : Identity ⊥ → ⊥
    α (identity ())
