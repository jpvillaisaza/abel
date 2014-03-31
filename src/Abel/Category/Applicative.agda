------------------------------------------------------------------------------
-- Abel: A brother of Cain
--
-- Applicative functors
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Category.Applicative where

open import Abel.Category.Functor using (Functor; mkFunctor)

open import Function using (id; _∘_; _$_)

open import Relation.Binary.PropositionalEquality as PropositionalEquality

------------------------------------------------------------------------------
-- Definition

record Applicative (F : Set → Set) : Set₁ where
  constructor
    mkApplicative

  infixl 4 _<*>_

  field
    pure  : ∀ {A} → A → F A
    _<*>_ : ∀ {A B} → F (A → B) → F A → F B

    pure-id    : ∀ {A} (fx : F A) → pure id <*> fx ≡ id fx

    pure-∘     : ∀ {A B C} (fg : F (B → C)) (ff : F (A → B)) (fx : F A) →
                 pure (λ g f → g ∘ f) <*> fg <*> ff <*> fx ≡ fg <*> (ff <*> fx)

    pure-hom   : ∀ {A B} (f : A → B) (x : A) → pure f <*> pure x ≡ pure (f x)

    pure-inter : ∀ {A B} (ff : F (A → B)) (x : A) →
                 ff <*> pure x ≡ pure (λ f → f x) <*> ff

------------------------------------------------------------------------------
-- An applicative functor is a functor

  functor : Functor F
  functor = mkFunctor fmap fmap-id fmap-∘
    where
      fmap : ∀ {A B} → (A → B) → F A → F B
      fmap f fx = pure f <*> fx

      fmap-id : ∀ {A} (fx : F A) → fmap id fx ≡ id fx
      fmap-id = pure-id

      fmap-∘ : ∀ {A B C} {g : B → C} {f : A → B} (fx : F A) →
               fmap (g ∘ f) fx ≡ (fmap g ∘ fmap f) fx
      fmap-∘ {g = g} {f} fx = sym $
        begin
          pure g <*> (pure f <*> fx)
            ≡⟨ sym (pure-∘ (pure g) (pure f) fx) ⟩
          pure (λ g f → g ∘ f) <*> pure g <*> pure f <*> fx
            ≡⟨ cong (λ x → x <*> pure f <*> fx) (pure-hom (λ g f → g ∘ f) g) ⟩
          pure (λ f → g ∘ f) <*> pure f <*> fx
            ≡⟨ cong (λ x → x <*> fx) (pure-hom (λ f → g ∘ f) f) ⟩
          pure (λ x → g (f x)) <*> fx
        ∎
          where
            open PropositionalEquality.≡-Reasoning
