------------------------------------------------------------------------------
-- Abel: A brother of Cain
--
-- The List monad and Kleisli triple
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.List.Monad where

open import Abel.Category.Functor
open import Abel.Category.Monad
open import Abel.Data.List using (concat)
open import Abel.Data.List.Functor using (functor)
open import Abel.Data.List.Properties using (++-[]; concat-++-commute)

open import Data.List using (List; []; _∷_; map; _++_)
open import Data.List.Properties using (map-++-commute)

open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

------------------------------------------------------------------------------
-- The List monad

monad' : Monad' functor
monad' = mkMonad' return join associativity unity-left unity-right
                  naturality-return naturality-join
  where
    return : {A : Set} → A → List A
    return x = x ∷ []

    join : {A : Set} → List (List A) → List A
    join = concat

    open Functor functor using (fmap)

    associativity : {A : Set} (xsss : List (List (List A))) →
                    join (join xsss) ≡ join (fmap join xsss)
    associativity []                        = refl
    associativity ([] ∷ xsss)               = associativity xsss
    associativity (([] ∷ xss) ∷ xsss)       = associativity (xss ∷ xsss)
    associativity (((x ∷ xs) ∷ xss) ∷ xsss) =
      cong (_∷_ x) (associativity ((xs ∷ xss) ∷ xsss))

    unity-left : {A : Set} (xs : List A) → join (return xs) ≡ xs
    unity-left []       = refl
    unity-left (x ∷ xs) = cong (_∷_ x) (unity-left xs)

    unity-right : {A : Set} (xs : List A) → join (fmap return xs) ≡ xs
    unity-right []       = refl
    unity-right (x ∷ xs) = cong (_∷_ x) (unity-right xs)

    naturality-return : {A B : Set} {f : A → List B} (x : A) →
                        return (f x) ≡ fmap f (return x)
    naturality-return _ = refl

    naturality-join : {A B : Set} {f : A → List B} (xss : List (List A)) →
                      join (fmap (fmap f) xss) ≡ fmap f (join xss)
    naturality-join         []               = refl
    naturality-join         ([] ∷ xss)       = naturality-join xss
    naturality-join {f = f} ((x ∷ xs) ∷ xss) =
      cong (_∷_ (f x)) (naturality-join (xs ∷ xss))

------------------------------------------------------------------------------
-- The List Kleisli triple

monad : Monad List
monad = mkMonad return bind associativity unity-left unity-right
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
