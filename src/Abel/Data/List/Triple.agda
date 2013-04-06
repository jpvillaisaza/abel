------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- TODO
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.List.Triple where

open import Abel.Category.Triple using (Triple; mkTriple)
open import Abel.Data.List using (concat)
open import Abel.Data.List.Properties using (++-[]; concat-++-commute)

open import Data.List using (List; []; _∷_; map; _++_)
open import Data.List.Properties using (map-++-commute)

open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

------------------------------------------------------------------------------
-- TODO

triple : Triple List
triple = mkTriple return bind associativity unity-left unity-right
  where
    return : {A : Set} → A → List A
    return x = x ∷ []

    bind : {A B : Set} → (A → List B) → List A → List B
    bind f xs = concat (map f xs)

    associativity : {A B C : Set} {f : A → List B} {g : B → List C}
                    (xs : List A) → bind g (bind f xs) ≡ bind (bind g ∘ f) xs
    associativity             []       = refl
    associativity {f = f} {g} (x ∷ xs) =
      begin
        concat (map g (f x ++ concat (map f xs)))
          ≡⟨ cong concat (map-++-commute g (f x) (concat (map f xs))) ⟩
        concat (map g (f x) ++ map g (concat (map f xs)))
          ≡⟨ concat-++-commute (map g (f x)) (map g (concat (map f xs))) ⟩
        concat (map g (f x)) ++ concat (map g (concat (map f xs)))
          ≡⟨ cong (_++_ (concat (map g (f x)))) (associativity xs) ⟩
        concat (map g (f x)) ++ concat (map (bind g ∘ f) xs)
      ∎
        where open Relation.Binary.PropositionalEquality.≡-Reasoning

    unity-left : {A B : Set} {f : A → List B} (x : A) →
                 bind f (return x) ≡ f x
    unity-left {f = f} x = ++-[] (f x)

    unity-right : {A : Set} (xs : List A) → bind return xs ≡ xs
    unity-right []       = refl
    unity-right (x ∷ xs) = cong (_∷_ x) (unity-right xs)
