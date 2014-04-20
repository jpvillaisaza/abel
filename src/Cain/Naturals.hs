------------------------------------------------------------------------------
-- Category Theory Applied to Functional Programming
--
-- Chapter 5 Natural Transformations
------------------------------------------------------------------------------

module Cain.Naturals where

import Prelude ()

import Cain.Functors (Maybe(Nothing, Just))

infixr 5 ++

-- The head function
head :: [a] -> Maybe a
head []    = Nothing
head (x:_) = Just x

-- The last function
last :: [a] -> Maybe a
last []     = Nothing
last (x:[]) = Just x
last (_:xs) = last xs

-- The (++) function as defined in GHC.Base.
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : xs ++ ys

-- The concat function.
concat :: [[a]] -> [a]
concat []       = []
concat (xs:xss) = xs ++ concat xss
