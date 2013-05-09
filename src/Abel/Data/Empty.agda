------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- TODO
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Empty where

open import Data.Empty using (⊥)

------------------------------------------------------------------------------
-- TODO

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()
