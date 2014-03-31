------------------------------------------------------------------------------
-- Abel: A brother of Cain
--
-- The ⊥ (empty) type
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Empty where

open import Data.Empty using (⊥)

------------------------------------------------------------------------------
-- The ⊥ (empty) type is the initial object

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()
