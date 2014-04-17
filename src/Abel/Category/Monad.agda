------------------------------------------------------------------------------
-- Abel: A brother of Cain
--
-- Monads and Kleisli triples
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Category.Monad where

open import Abel.Category.Functor

open import Function using (_∘_; id)

open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------------
-- Definition (Monad)

record Monad' {M : Set → Set} (functor : Functor M) : Set₁ where

  constructor mkMonad'

  open Functor functor using (fmap)

  field

    return : {A : Set} → A → M A

    join   : {A : Set} → M (M A) → M A

    associativity : {A : Set} (mmmx : M (M (M A))) →
                    join (join mmmx) ≡ join (fmap join mmmx)

    unity-left    : {A : Set} (mx : M A) → join (return mx) ≡ mx

    unity-right   : {A : Set} (mx : M A) → join (fmap return mx) ≡ mx

    naturality-return : {A B : Set} {f : A → M B} (x : A) →
                        return (f x) ≡ fmap f (return x)

    naturality-join   : {A B : Set} {f : A → M B} (mmx : M (M A)) →
                        join (fmap (fmap f) mmx) ≡ fmap f (join mmx)

  bind : {A B : Set} → (A → M B) → M A → M B
  bind f = join ∘ fmap f

------------------------------------------------------------------------------
-- Definition (Kleisli triple or monad in extension form)

record Monad'' (M : Set → Set) : Set₁ where

  constructor mkMonad''

  field

    return : {A : Set} → A → M A

    bind   : {A B : Set} → (A → M B) → M A → M B

    associativity : {A B C : Set} {f : A → M B} {g : B → M C} (mx : M A) →
                    bind g (bind f mx) ≡ bind (bind g ∘ f) mx

    unity-left    : {A B : Set} {f : A → M B} (x : A) →
                    bind f (return x) ≡ f x

    unity-right   : {A : Set} (mx : M A) → bind return mx ≡ mx

  infixr 1 _=<<_

  _=<<_ : {A B : Set} → (A → M B) → M A → M B
  _=<<_ = bind

  infixl 1 _>>=_ _>>_

  _>>=_ : {A B : Set} → M A → (A → M B) → M B
  mx >>= f = bind f mx

  _>>_ : {A B : Set} → M A → M B → M B
  mx >> my = mx >>= λ _ → my

  fmap : {A B : Set} → (A → B) → M A → M B
  fmap f = bind (return ∘ f)

  join : ∀ {A} → M (M A) → M A
  join = bind id
