------------------------------------------------------------------------------
-- Abel: a brother of Cain                https://github.com/jpvillaisaza/abel
--
-- List is a functor
------------------------------------------------------------------------------

module Abel.Data.List.Functor where

open import Abel.Category.Functor using (Functor; mkFunctor)

open import Data.List using (List; []; _∷_)

open import Function using (id; _∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

functor : Functor List
functor = mkFunctor fmap fmap-id fmap-∘
  where
    fmap : ∀ {A B} → (A → B) → List A → List B
    fmap _ []       = []
    fmap f (x ∷ xs) = f x ∷ fmap f xs

    fmap-id : ∀ {A} (xs : List A) → fmap id xs ≡ id xs
    fmap-id []       = refl
    fmap-id (x ∷ xs) = cong (_∷_ x) (fmap-id xs)

    fmap-∘ : ∀ {A B C} {f : A → B} {g : B → C}
             (xs : List A) → fmap (g ∘ f) xs ≡ (fmap g ∘ fmap f) xs
    fmap-∘ []                   = refl
    fmap-∘ {f = f} {g} (x ∷ xs) = cong (_∷_ (g (f x))) (fmap-∘ xs)
