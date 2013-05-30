------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- Natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Nat where

open import Data.Nat using (ℕ; zero; suc; fold)

------------------------------------------------------------------------------
-- Folds

add : ℕ → ℕ → ℕ
add m n = fold n suc m

mul : ℕ → ℕ → ℕ
mul m n = fold zero (add n) m
