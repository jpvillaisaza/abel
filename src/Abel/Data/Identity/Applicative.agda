------------------------------------------------------------------------------
-- Abel: A brother of Cain
--
-- The Identity applicative functor
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Identity.Applicative where

open import Abel.Category.Applicative using (Applicative; mkApplicative)
open import Abel.Data.Identity using (Identity; identity)

open import Function using (id; _∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------------
-- The Identity applicative endofunctor

applicative : Applicative Identity
applicative = mkApplicative pure _<*>_ pure-id pure-∘ (λ _ _ → refl) pure-inter
  where
    pure : ∀ {A} → A → Identity A
    pure = identity

    infixl 4 _<*>_

    _<*>_ : ∀ {A B} → Identity (A → B) → Identity A → Identity B
    identity f <*> identity x = identity (f x)

    pure-id : ∀ {A} (ix : Identity A) → pure id <*> ix ≡ id ix
    pure-id (identity _) = refl

    pure-∘ : ∀ {A B C} (ig : Identity (B → C)) (if : Identity (A → B))
             (ix : Identity A) →
             pure (λ g f → g ∘ f) <*> ig <*> if <*> ix ≡ ig <*> (if <*> ix)
    pure-∘ (identity _) (identity _) (identity _) = refl


    pure-inter : ∀ {A B} (if : Identity (A → B)) (x : A) →
                 if <*> pure x ≡ pure (λ f → f x) <*> if
    pure-inter (identity _) _ = refl
