------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- TODO
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Unit where

open import Data.Unit using (⊤; tt)

------------------------------------------------------------------------------
-- TODO

unit : {A : Set} → A → ⊤
unit _ = tt
