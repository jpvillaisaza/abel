------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- TODO
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.List.Monad where

open import Abel.Category.Functor
open import Abel.Category.Monad using (Monad; mkMonad)
open import Abel.Data.List using (concat)
open import Abel.Data.List.Functor using (functor)

open import Data.List using (List; []; _∷_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

------------------------------------------------------------------------------
-- TODO

monad : Monad functor
monad = mkMonad return join associativity unity-left unity-right
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
