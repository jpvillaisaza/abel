------------------------------------------------------------------------------
-- Category Theory Applied to Functional Programming
--
-- Chapter 2 Categories
------------------------------------------------------------------------------

module Cain.Categories where

import Prelude ()

infixr 9 .

------------------------------------------------------------------------------
-- 2.2 A Category for Haskell

-- Hask is the category of Haskell types and functions.

-- The Bool type as defined in GHC.Types.
data Bool = False | True

-- The Nat type.
data Nat = Zero | Succ Nat

-- Haskell types have bottom.
undefined :: a
undefined = undefined

-- Convention 1. By Haskell types, we mean Haskell types without
-- bottom values.

-- The not function as defined in GHC.Classes.
not :: Bool -> Bool
not False = True
not True  = False

-- The isZero function.
isZero :: Nat -> Bool
isZero Zero = True
isZero _    = False

-- The identity function as defined in GHC.Base.
id :: a -> a
id x = x

-- Function composition as defined in GHC.Base.
(.) :: (b -> c) -> (a -> b) -> a -> c
g . f = \x -> g (f x)
