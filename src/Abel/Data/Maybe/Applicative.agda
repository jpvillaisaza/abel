------------------------------------------------------------------------------
-- Abel: a brother of Cain                https://github.com/jpvillaisaza/abel
--
-- The Maybe applicative functor
------------------------------------------------------------------------------

-- (Tested with Agda 2.3.2 and the Agda standard library 0.7.)

module Abel.Data.Maybe.Applicative where

open import Abel.Category.Applicative
open import Abel.Data.Maybe.Functor

open import Data.Maybe using (Maybe; just; nothing)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------------
-- Maybe is an applicative functor

applicative : Applicative Maybe
applicative = mkApplicative pure _<*>_ pure-id pure-∘ pure-hom pure-inter
  where
    infixl 4 _<*>_

    pure : ∀ {A} → A → Maybe A
    pure = just

    _<*>_ : ∀ {A B} → Maybe (A → B) → Maybe A → Maybe B
    just f <*> just x = just (f x)
    _      <*> _      = nothing

    pure-id : ∀ {A} (mx : Maybe A) → pure id <*> mx ≡ id mx
    pure-id (just _) = refl
    pure-id nothing  = refl

    pure-∘ : ∀ {A B C}
             (mg : Maybe (B → C)) (mf : Maybe (A → B)) (mx : Maybe A) →
             pure (λ g f → g ∘ f) <*> mg <*> mf <*> mx ≡ mg <*> (mf <*> mx)
    pure-∘ (just _) (just _) (just _) = refl
    pure-∘ (just _) (just _) nothing  = refl
    pure-∘ (just _) nothing  _        = refl
    pure-∘ nothing  _        _        = refl

    pure-hom : ∀ {A B} (f : A → B) (x : A) → pure f <*> pure x ≡ pure (f x)
    pure-hom _ _ = refl

    pure-inter : ∀ {A B} (mf : Maybe (A → B)) (x : A) →
                 mf <*> pure x ≡ pure (λ f → f x) <*> mf
    pure-inter (just _) _ = refl
    pure-inter nothing  _ = refl
