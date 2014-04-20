------------------------------------------------------------------------------
-- Category Theory Applied to Functional Programming
--
-- Chapter 3 Constructions
------------------------------------------------------------------------------

module Cain.Constructions where

import Prelude ()

------------------------------------------------------------------------------
-- 3.2 Initial and Terminal Objects

-- The Void type.
data Void

-- The absurd function.
absurd :: Void -> a
absurd = absurd

-- The unit type as defined in GHC.Tuple.
-- data () = ()

-- The unit function.
unit :: a -> ()
unit _ = ()

------------------------------------------------------------------------------
-- 3.3 Products and Coproducts

-- Tuples as defined in GHC.Tuple.
-- data (,) a b = (,) a b

-- The fst function as defined in Data.Tuple.
fst :: (a,b) -> a
fst (x,_) = x

-- The snd function as defined in Data.Tuple.
snd :: (a,b) -> b
snd (_,y) = y

-- The fork function.
fork :: (c -> a) -> (c -> b) -> c -> (a,b)
fork f g z = (f z, g z)

-- The Either type as defined in Data.Either.
data Either a b = Left a | Right b

-- The either function as defined in Data.Either.
either :: (a -> c) -> (b -> c) -> Either a b -> c
either f _ (Left x)  = f x
either _ g (Right y) = g y
