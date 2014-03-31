------------------------------------------------------------------------------
-- Abel: A brother of Cain
--
-- The initial algebra over the Identity endofunctor
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Empty.Algebra where

open import Abel.Category.Algebra using (Algebra; mkAlgebra)
open import Abel.Data.Identity using (Identity; identity)
open import Abel.Data.Identity.Functor renaming (functor to functorI)

open import Data.Empty using (⊥)

------------------------------------------------------------------------------
-- The algebra

algebra : Algebra functorI
algebra = mkAlgebra ⊥ α
  where
    α : Identity ⊥ → ⊥
    α (identity ())
