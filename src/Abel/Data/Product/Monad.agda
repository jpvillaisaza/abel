------------------------------------------------------------------------------
-- Abel: a brother of Cain                https://github.com/jpvillaisaza/abel
--
-- The (_×_ A) monad
------------------------------------------------------------------------------

-- (Tested with Agda 2.3.2 and the Agda standard library 0.7.)

module Abel.Data.Product.Monad where

open import Abel.Category.Applicative
open import Abel.Category.Functor
open import Abel.Category.Monad
open import Abel.Data.Product.Applicative

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (id; _∘_; _$_)
open import Relation.Binary.PropositionalEquality as PropositionalEquality

------------------------------------------------------------------------------
-- (_×_ A) is a monad

monad : ∀ {A} {monoid : Monoid A} →
        Monad (_×_ A) {applicative {monoid = monoid}}
monad {A} {monoid} = mkMonad _>>=_
                             return-left-id return-right-id >>=-assoc >>=-fmap
  where
    open Applicative (applicative {monoid = monoid})
    open Functor functor
    open Monoid monoid

    infixl 1 _>>=_

    return : ∀ {B} → B → A × B
    return = pure

    _>>=_ : ∀ {B C} → A × B → (B → A × C) → A × C
    (x , y) >>= g = (mappend x (proj₁ (g y))) , (proj₂ (g y))

    return-left-id : ∀ {B C} (y : B) (g : B → A × C) → (return y >>= g) ≡ g y
    return-left-id y g = cong (λ x → x , proj₂ (g y)) (left-id (proj₁ (g y)))

    return-right-id : ∀ {B} (x,y : A × B) → (x,y >>= return) ≡ x,y
    return-right-id (x , y) = cong (λ x → x , y) (right-id x)

    >>=-assoc : ∀ {B C D} (x,y : A × B) (g : C → A × D) (f : B → A × C) →
                (x,y >>= λ x → f x >>= g) ≡ ((x,y >>= f) >>= g)
    >>=-assoc (x , y) g f =
      cong (λ x → x , proj₂ (g (proj₂ (f y))))
           (assoc x (proj₁ (f y)) (proj₁ (g (proj₂ (f y)))))

    >>=-fmap : ∀ {B C} (g : B → C) (x,y : A × B) →
               fmap g x,y ≡ (x,y >>= pure ∘ g)
    >>=-fmap g (x , y) =
      cong (λ x → x , g y) (trans (left-id x) (sym (right-id x)))
