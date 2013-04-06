------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- Monads and Kleisli triples
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Category.Triple where

open import Abel.Category.Functor

open import Function using (id; _∘_; _$_)

open import Relation.Binary.PropositionalEquality --using (_≡_; refl; cong; cong₂; sym)

------------------------------------------------------------------------------
-- Definition (Monad)

record Monad {M : Set → Set} (functor : Functor M) : Set₁ where

  constructor mkMonad

  open Functor functor using (fmap)

  field

    return : {A : Set} → A → M A

    join   : {A : Set} → M (M A) → M A

    assoc      : {A : Set} (mmmx : M (M (M A))) →
                 join (join mmmx) ≡ join (fmap join mmmx)

    unit-left  : {A : Set} (mx : M A) → join (return mx) ≡ mx

    unit-right : {A : Set} (mx : M A) → join (fmap return mx) ≡ mx

  bind : {A B : Set} → (A → M B) → M A → M B
  bind f = join ∘ fmap f

------------------------------------------------------------------------------
-- Definition (Kleisli triple)

record Triple (M : Set → Set) : Set₁ where

  constructor mkTriple

  field

    return : {A : Set} → A → M A

    bind   : {A B : Set} → (A → M B) → M A → M B

    assoc      : {A B C : Set} {f : A → M B} {g : B → M C} (mx : M A) →
                 bind g (bind f mx) ≡ bind (bind g ∘ f) mx

    unit-left  : {A B : Set} {f : A → M B} (x : A) → bind f (return x) ≡ f x

    unit-right : {A : Set} (mx : M A) → bind return mx ≡ mx

  infixl 1 _>>=_

  _>>=_ : {A B : Set} → M A → (A → M B) → M B
  mx >>= f = bind f mx

  fmap : {A B : Set} → (A → B) → M A → M B
  fmap f = bind (return ∘ f)

  join : ∀ {A} → M (M A) → M A
  join = bind id

triple : {M : Set → Set} {functor : Functor M} → Monad functor → Triple M
triple {M} {functor} monad =
  mkTriple return bind assoc-t unit-left-t unit-right
    where
      open Functor functor
      open Monad monad

      assoc-t : {A B C : Set} {f : A → M B} {g : B → M C} (mx : M A) →
                bind g (bind f mx) ≡ bind (bind g ∘ f) mx
      assoc-t {f = f} {g} mx =
        begin
          join (fmap g (join (fmap f mx)))
            ≡⟨ {!!} ⟩
          {!!}
            ≡⟨ {!!} ⟩
          {!!}
            ≡⟨ {!!} ⟩
          {!!}
            ≡⟨ {!!} ⟩
          {!!}
            ≡⟨ {!!} ⟩
          {!!}
            ≡⟨ {!!} ⟩
          {!!}
            ≡⟨ {!!} ⟩
          {!!}
            ≡⟨ {!!} ⟩
          join ((fmap join ∘ fmap (fmap g ∘ f)) mx)
            ≡⟨ {!!} ⟩
          join (fmap (join ∘ fmap g ∘ f) mx)
        ∎
          where open Relation.Binary.PropositionalEquality.≡-Reasoning

      sd : {A B : Set} {f : A → M B} (x : A) →
           fmap f (return x) ≡ return (f x)
      sd x = {!!}

      unit-left-t : {A B : Set} {f : A → M B} (x : A) →
                    bind f (return x) ≡ f x
      unit-left-t {f = f} x =
        begin
          join (fmap f (return x))
            ≡⟨ cong join {!!} ⟩
          join (return (f x))
            ≡⟨ unit-left (f x) ⟩
          f x
        ∎
          where open Relation.Binary.PropositionalEquality.≡-Reasoning

functor : {M : Set → Set} → Triple M → Functor M
functor {M} triple = mkFunctor fmap unit-right fmap-∘
  where
    open Triple triple

    sd : {B C : Set} {g : B → C} → return ∘ g ≡ bind (return ∘ g) ∘ return
    sd = λ {B} {C} {g} → {!!}

    fmap-∘ : {A B C : Set} {f : A → B} {g : B → C} (mx : M A) →
             fmap (g ∘ f) mx ≡ fmap g (fmap f mx)
    fmap-∘ {f = f} {g} mx =
      begin
        fmap (g ∘ f) mx
          ≡⟨ refl ⟩
        bind (return ∘ g ∘ f) mx
          ≡⟨ refl ⟩
        bind ((return ∘ g) ∘ f) mx
          ≡⟨ refl ⟩
        bind ((λ y → return (g y)) ∘ f) mx
          ≡⟨ {!!} ⟩
        bind ((λ y → bind (return ∘ g) (return y)) ∘ f) mx
          ≡⟨ refl ⟩
        bind ((bind (return ∘ g) ∘ return) ∘ f) mx
          ≡⟨ refl ⟩
        bind (bind (return ∘ g) ∘ return ∘ f) mx
          ≡⟨ sym (assoc mx) ⟩
        bind (return ∘ g) (bind (return ∘ f) mx)
          ≡⟨ refl ⟩
        bind (return ∘ g) (fmap f mx)
          ≡⟨ refl ⟩
        fmap g (fmap f mx)
      ∎
        where open Relation.Binary.PropositionalEquality.≡-Reasoning

      -- begin
      --   bind (return ∘ g) (bind (return ∘ f) mx)
      --     ≡⟨ assoc mx ⟩
      --   bind (bind (return ∘ g) ∘ return ∘ f) mx
      --     ≡⟨ cong (λ x → bind ({!!} ∘ f) mx) (unit-left {f = return ∘ g} _) ⟩
      --   bind (return ∘ g ∘ f) mx
      -- ∎
      --   where open Relation.Binary.PropositionalEquality.≡-Reasoning

-- bind (return (g ∘ f)) mx ≡ bind (return g) (bind (return f) mx)

monad : {M : Set → Set} (triple : Triple M) → Monad (functor triple)
monad {M} triple = mkMonad return join assoc-m unit-left unit-right-m
  where
    open Triple triple

    assoc-m : {A : Set} (mmmx : M (M (M A))) →
              join (join mmmx) ≡ join (fmap join mmmx)
    assoc-m mmmx =
      begin
        bind id (bind id mmmx)
          ≡⟨ assoc mmmx ⟩
        bind (bind id) mmmx
          ≡⟨ cong (λ bind-id → bind bind-id mmmx) refl ⟩
        bind (bind id ∘ id) mmmx
          ≡⟨ cong (λ x → bind (bind id ∘ x) mmmx) (sym {!!}) ⟩
        bind (bind id ∘ return ∘ bind id) mmmx
          ≡⟨ {!!} ⟩
        bind id (bind (return ∘ bind id) mmmx)
          ≡⟨ refl ⟩
        bind id (fmap (bind id) mmmx)
          ≡⟨ refl ⟩
        bind id (fmap join mmmx)
          ≡⟨ refl ⟩
        join (fmap join mmmx)
      ∎
        where open Relation.Binary.PropositionalEquality.≡-Reasoning

    unit-right-m : {A : Set} (mx : M A) → join (fmap return mx) ≡ mx
    unit-right-m mx =
      begin
        join (fmap return mx)
          ≡⟨ refl ⟩
        bind id (bind (return ∘ return) mx)
          ≡⟨ assoc mx ⟩
        bind (bind id ∘ return ∘ return) mx
          ≡⟨ cong (λ x → bind (x ∘ return) mx) {!∀-extensionality!} ⟩
        bind return mx
          ≡⟨ unit-right mx ⟩
        mx
      ∎
        where open Relation.Binary.PropositionalEquality.≡-Reasoning

-- bind (λ x → x) (bind (λ x → return (return x)) mx) ≡ mx
