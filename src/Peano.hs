{- @ LIQUID "--ple-local" @-}
{- @ LIQUID "--ple" @-}

module Peano where

import Prelude hiding (min)

import Language.Haskell.Liquid.ProofCombinators

data N = Z | S N

{- @ measure toNat @-}
{- @ toNat :: N -> {v:Int | v >= 0} @-}
toNat :: N -> Int
toNat Z     = 0
toNat (S n) = 1 + (toNat n) 

{-@ reflect min @-}
{- @ min :: m:N -> N -> N / [toNat m] @-}
min :: N -> N -> N
min Z _ = Z
min _ Z = Z
min (S m) (S n) = S (min m n)

{- @ automatic-instances assocMin @-}
{-@ assocMin :: a:N -> b:N -> c:N ->
        { _:() | min (min a b) c == min a (min b c) } @-}
assocMin :: N -> N -> N -> Proof
assocMin Z _ _ = trivial
assocMin _ Z _ = trivial
assocMin _ _ Z = trivial
assocMin (S a') (S b') (S c') = assocMin a' b' c'   


{- @ automatic-instances assocMin2 @-}
{-@ assocMin2 :: a:N -> b:N -> c:N ->
        { _:() | min (min a b) c == min a (min b c) } @-}
assocMin2 :: N -> N -> N -> Proof
assocMin2 = \a b c -> case a of
    Z -> case b of  
            Z -> case c of 
                    Z -> trivial
                    (S c') -> trivial
            (S b') -> case c of 
                    Z -> trivial
                    (S c') -> trivial
    (S a') -> case b of  
            Z -> case c of 
                    Z -> trivial
                    (S c') -> trivial
            (S b') -> case c of 
                    Z -> trivial
                    (S c') -> assocMin2 a' b' c'
        
