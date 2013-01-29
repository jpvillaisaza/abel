------------------------------------------------------------------------------
-- Abel: a brother of Cain                https://github.com/jpvillaisaza/abel
--
-- The (_⊎_ A) applicative functor
------------------------------------------------------------------------------

-- (Tested with Agda 2.3.2 and the Agda standard library 0.7.)

module Abel.Data.Sum.Applicative where

open import Abel.Category.Applicative

open import Data.Sum
open import Function
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- (_⊎_ A) is an applicative functor

applicative : ∀ {A} → Applicative (_⊎_ A)
applicative {A} = mkApplicative pure _<*>_ pure-id pure-∘ pure-hom pure-inter
  where

    infixl 4 _<*>_

    pure : ∀ {B} → B → A ⊎ B
    pure = inj₂

    _<*>_ : ∀ {B C} → A ⊎ (B → C) → A ⊎ B → A ⊎ C
    inj₁ x <*> _      = inj₁ x
    inj₂ _ <*> inj₁ x = inj₁ x
    inj₂ g <*> inj₂ y = inj₂ (g y)

    pure-id : ∀ {B} (x⊎y : A ⊎ B) → pure id <*> x⊎y ≡ id x⊎y
    pure-id (inj₁ _) = refl
    pure-id (inj₂ _) = refl

    pure-∘ : ∀ {B C D} (x⊎h : A ⊎ (C → D)) (x⊎g : A ⊎ (B → C)) (x⊎y : A ⊎ B) →
             pure (λ g f → g ∘ f) <*> x⊎h <*> x⊎g <*> x⊎y
               ≡ x⊎h <*> (x⊎g <*> x⊎y)
    pure-∘ (inj₁ _) _        _        = refl
    pure-∘ (inj₂ _) (inj₁ _) _        = refl
    pure-∘ (inj₂ _) (inj₂ _) (inj₁ _) = refl
    pure-∘ (inj₂ _) (inj₂ _) (inj₂ _) = refl

    pure-hom : ∀ {B C} (g : B → C) (y : B) → pure g <*> pure y ≡ pure (g y)
    pure-hom _ _ = refl

    pure-inter : ∀ {B C} (x⊎g : A ⊎ (B → C)) (y : B) →
                 x⊎g <*> pure y ≡ pure (λ f → f y) <*> x⊎g
    pure-inter (inj₁ _) _ = refl
    pure-inter (inj₂ _) _ = refl
