------------------------------------------------------------------------------
-- Abel: A brother of Cain
--
-- Properties concerning lists
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.List.Properties where

open import Abel.Data.List using (concat)

open import Data.List using (List; []; _∷_; _++_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

------------------------------------------------------------------------------
-- The properties

++-[] : {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-[] []       = refl
++-[] (x ∷ xs) = cong (_∷_ x) (++-[] xs)

++-assoc : {A : Set} (xs ys zs : List A) → xs ++ ys ++ zs ≡ (xs ++ ys) ++ zs
++-assoc []       _  _  = refl
++-assoc (x ∷ xs) ys zs = cong (_∷_ x) (++-assoc xs ys zs)

concat-++-commute : {A : Set} (xs ys : List (List A)) →
                    concat (xs ++ ys) ≡ concat xs ++ concat ys
concat-++-commute []         _   = refl
concat-++-commute (xs ∷ xss) yss =
  begin
    xs ++ concat (xss ++ yss)
      ≡⟨ cong (_++_ xs) (concat-++-commute xss yss) ⟩
    xs ++ concat xss ++ concat yss
      ≡⟨ ++-assoc xs (concat xss) (concat yss) ⟩
    (xs ++ concat xss) ++ concat yss
  ∎
    where open Relation.Binary.PropositionalEquality.≡-Reasoning
