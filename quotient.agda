{-# OPTIONS --cubical=uip #-}
module quotient where

open import Agda.Builtin.Nat

double : Nat → Nat → Set
double 0 0 = ⊤
