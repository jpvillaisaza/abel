------------------------------------------------------------------------------
-- Abel: a brother of Cain                https://github.com/jpvillaisaza/abel
--
-- The (_⇒_ A) applicative functor
------------------------------------------------------------------------------

-- (Tested with Agda 2.3.2 and the Agda standard library 0.7.)

module Abel.Function.Applicative where

open import Abel.Category.Applicative
open import Abel.Function

open import Function
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- (_⇒_ A) is an applicative functor

applicative : ∀ {A} → Applicative (_⇒_ A)
applicative {A} =
  mkApplicative
    pure _<*>_ (λ _ → refl) (λ _ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl)
  where
    pure : ∀ {B} → B → A → B
    pure y = λ _ → y -- const

    _<*>_ : ∀ {B C} → (A → B → C) → (A → B) → A → C
    g <*> f = λ x → g x (f x)

    pure-id : ∀ {B} (f : A → B) → pure id <*> f ≡ id f
    pure-id f = refl
