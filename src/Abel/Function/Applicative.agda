------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- TODO
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Function.Applicative where

open import Abel.Category.Applicative

open import Function
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- TODO

applicative : ∀ {A} → Applicative (λ B → A → B)
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
