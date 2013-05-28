------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- TODO
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Nat where

open import Data.Nat using (ℕ; zero; suc)

------------------------------------------------------------------------------
-- TODO

fold : {A : Set} → (A → A) → A → ℕ → A
fold h c zero    = c
fold h c (suc n) = h (fold h c n)
