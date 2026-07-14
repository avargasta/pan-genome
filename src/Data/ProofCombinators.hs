module Data.ProofCombinators where

{-@ assert :: b:{Bool | b} -> a -> {x:a | b} @-}
assert :: Bool -> a -> a
assert _ x = x


{-@ assume assume :: b:Bool -> a -> {x:a | b} @-}
assume :: Bool -> a -> a
assume _ x = x

{-@ (?) :: x:a -> p:b -> {v:a | v == x} @-}
(?) :: a -> b -> a
x ? _ = x
