------------------------------------------------------------------------------
-- Abel: A brother of Cain
--
-- The unit type
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Unit where

open import Data.Unit using (⊤; tt)

------------------------------------------------------------------------------
-- The ⊤ (unit) type

unit : {A : Set} → A → ⊤
unit _ = tt
