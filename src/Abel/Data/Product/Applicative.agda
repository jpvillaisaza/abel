------------------------------------------------------------------------------
-- Abel: A brother of Cain
--
-- The (_×_ A) applicative functor
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Product.Applicative where

open import Abel.Category.Applicative

open import Data.Product using (_×_; _,_)
open import Function using (id; _∘_; _$_)
open import Relation.Binary.PropositionalEquality as PropositionalEquality

------------------------------------------------------------------------------
-- Monoids

record Monoid (A : Set) : Set where
  field
    mempty  : A
    mappend : A → A → A

    left-id  : ∀ x → mappend mempty x ≡ x
    right-id : ∀ x → mappend x mempty ≡ x
    assoc    : ∀ x y z → mappend x (mappend y z) ≡ mappend (mappend x y) z

------------------------------------------------------------------------------
-- (_×_ A) is an applicative functor

applicative : ∀ {A} {monoid : Monoid A} → Applicative (_×_ A)
applicative {A} {monoid} = mkApplicative pure _<*>_
                                         pure-id pure-∘ pure-hom pure-inter
  where
    open Monoid monoid

    infixl 4 _<*>_

    pure : ∀ {B} → B → A × B
    pure y = mempty , y

    _<*>_ : ∀ {B C} → A × (B → C) → A × B → A × C
    (x₁ , g) <*> (x₂ , y) = mappend x₁ x₂ , g y

    pure-id : ∀ {B} (x,y : A × B) → pure id <*> x,y ≡ id x,y
    pure-id (x , y) = cong (λ x → x , y) (left-id x)

    pure-∘ : ∀ {B C D} (x,h : A × (C → D)) (x,g : A × (B → C)) (x,y : A × B) →
             pure (λ h g → h ∘ g) <*> x,h <*> x,g <*> x,y ≡ x,h <*> (x,g <*> x,y)
    pure-∘ (x₁ , h) (x₂ , g) (x₃ , y) = cong (λ x → x , h (g y)) $
      begin
        mappend (mappend (mappend mempty x₁) x₂) x₃
          ≡⟨ cong (λ x → mappend (mappend x x₂) x₃) (left-id x₁) ⟩
        mappend (mappend x₁ x₂) x₃
          ≡⟨ sym (assoc x₁ x₂ x₃) ⟩
        mappend x₁ (mappend x₂ x₃)
      ∎
        where
          open PropositionalEquality.≡-Reasoning

    pure-hom : ∀ {B C} (g : B → C) (y : B) → pure g <*> pure y ≡ pure (g y)
    pure-hom g y = cong (λ x → x , g y) (left-id mempty)

    pure-inter : ∀ {B C} (x,g : A × (B → C)) (y : B) →
                 x,g <*> pure y ≡ pure (λ g → g y) <*> x,g
    pure-inter (x , g) y =
      cong (λ x → x , g y) (trans (right-id x) (sym (left-id x)))
