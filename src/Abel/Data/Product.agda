------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
-- Products
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Data.Product where

------------------------------------------------------------------------------
-- TODO

infixr 4 _,_

infixr 2 _×_

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

proj₁ : {A B : Set} → A × B → A
proj₁ (x , _) = x

proj₂ : {A B : Set} → A × B → B
proj₂ (_ , y) = y

⟨_,_⟩ : {A B C : Set} → (C → A) → (C → B) → C → A × B
⟨_,_⟩ f g z = f z , g z

------------------------------------------------------------------------------
--

uncurry : {A B C : Set} → (A → B → C) → A × B → C
uncurry f (x , y) = f x y
