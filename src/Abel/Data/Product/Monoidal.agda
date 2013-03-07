------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
--
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Product.Monoidal where

open import Abel.Category.Functor
open import Abel.Category.Monoidal
open import Abel.Data.Product.Functor

open import Data.Product hiding (map)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- Monoids

record Monoid (A : Set) : Set where
  field
    mempty  : A
    mappend : A → A → A

    mleft-id  : ∀ x → mappend mempty x ≡ x
    mright-id : ∀ x → mappend x mempty ≡ x
    massoc    : ∀ x y z → mappend x (mappend y z) ≡ mappend (mappend x y) z

------------------------------------------------------------------------------
-- (_×_ A) is a monoidal functor

monoidal : ∀ {A} {monoid : Monoid A} → Monoidal (_×_ A) {functor}
monoidal {A} {monoid} = mkMonoidal unit _*_
                                   (λ _ _ → refl) left-id right-id *-assoc
  where
    open Functor functor
    open Monoid monoid

    unit : A × ⊤
    unit = mempty , tt

    _*_ : ∀ {B C} → A × B → A × C → A × B × C
    (x₁ , y) * (x₂ , z) = mappend x₁ x₂ , y , z

    nat-* : ∀ {B C D E : Set}
            {g : B → C} {i : D → E} (x,y : A × B) (x,w : A × D) →
            fmap (map g i) (x,y * x,w) ≡ fmap g x,y * fmap i x,w
    nat-* (_ , _) (_ , _) = refl

    left-id : ∀ {C} (x,z : A × C) → fmap proj₂ (unit * x,z) ≡ x,z
    left-id (x , z) = cong (λ x → x , z) (mleft-id x)

    right-id : ∀ {B} (x,y : A × B) → fmap proj₁ (x,y * unit) ≡ x,y
    right-id (x , y) = cong (λ x → x , y) (mright-id x)

    *-assoc : ∀ {B C D} (x,y : A × B) (x,z : A × C) (x,w : A × D) →
              fmap assoc (x,y * (x,z * x,w)) ≡ (x,y * x,z) * x,w
    *-assoc (x₁ , y) (x₂ , z) (x₃ , w) =
      cong (λ x → x , (y , z) , w) (massoc x₁ x₂ x₃)
