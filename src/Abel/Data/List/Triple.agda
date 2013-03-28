------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- The List monad and Kleisli triple
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.List.Triple where

open import Abel.Category.Functor
open import Abel.Category.Triple using (Monad; mkMonad; Triple; mkTriple)
open import Abel.Data.List using (concat)
open import Abel.Data.List.Functor using (functor)
open import Abel.Data.List.Properties using (++-[]; concat-++-commute)

open import Data.List using (List; []; _∷_; map; _++_)
open import Data.List.Properties using (map-++-commute)

open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

------------------------------------------------------------------------------
-- The List monad

monad : Monad functor
monad = mkMonad return join assoc unit-left unit-right
  where
    return : {A : Set} → A → List A
    return x = x ∷ []

    join : {A : Set} → List (List A) → List A
    join = concat

    open Functor functor

    assoc : {A : Set} (xsss : List (List (List A))) →
                    join (join xsss) ≡ join (fmap join xsss)
    assoc []                        = refl
    assoc ([] ∷ xsss)               = assoc xsss
    assoc (([] ∷ xss) ∷ xsss)       = assoc (xss ∷ xsss)
    assoc (((x ∷ xs) ∷ xss) ∷ xsss) =
      cong (_∷_ x) (assoc ((xs ∷ xss) ∷ xsss))

    unit-left : {A : Set} (xs : List A) → join (return xs) ≡ xs
    unit-left []       = refl
    unit-left (x ∷ xs) = cong (_∷_ x) (unit-left xs)

    unit-right : {A : Set} (xs : List A) → join (fmap return xs) ≡ xs
    unit-right []       = refl
    unit-right (x ∷ xs) = cong (_∷_ x) (unit-right xs)

------------------------------------------------------------------------------
-- The List Kleisli triple

triple : Triple List
triple = mkTriple return bind assoc unit-left unit-right
  where
    return : {A : Set} → A → List A
    return x = x ∷ []

    bind : {A B : Set} → (A → List B) → List A → List B
    bind f xs = concat (map f xs)

    assoc : {A B C : Set} {f : A → List B} {g : B → List C} (xs : List A) →
            bind g (bind f xs) ≡ bind (bind g ∘ f) xs
    assoc             []       = refl
    assoc {f = f} {g} (x ∷ xs) =
      begin
        concat (map g (f x ++ concat (map f xs)))
          ≡⟨ cong concat (map-++-commute g (f x) (concat (map f xs))) ⟩
        concat (map g (f x) ++ map g (concat (map f xs)))
          ≡⟨ concat-++-commute (map g (f x)) (map g (concat (map f xs))) ⟩
        concat (map g (f x)) ++ concat (map g (concat (map f xs)))
          ≡⟨ cong (_++_ (concat (map g (f x)))) (assoc xs) ⟩
        concat (map g (f x)) ++ concat (map (bind g ∘ f) xs)
      ∎
        where open Relation.Binary.PropositionalEquality.≡-Reasoning

    unit-left : {A B : Set} {f : A → List B} (x : A) → bind f (return x) ≡ f x
    unit-left {f = f} x = ++-[] (f x)

    unit-right : {A : Set} (xs : List A) → bind return xs ≡ xs
    unit-right []       = refl
    unit-right (x ∷ xs) = cong (_∷_ x) (unit-right xs)
