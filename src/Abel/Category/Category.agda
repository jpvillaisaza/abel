------------------------------------------------------------------------------
-- Abel: a brother of Cain                https://github.com/jpvillaisaza/abel
--
-- Categories
------------------------------------------------------------------------------

module Abel.Category.Category where

record Category (_⇒_ : Set → Set → Set) : Set₁ where

  constructor mkCategory

  infixr 9 _∘_

  field

    id  : ∀ {A} → A ⇒ A

    _∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C
