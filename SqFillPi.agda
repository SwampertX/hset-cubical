{-# OPTIONS --cubical=no-glue #-}

open import Helper

module SqFillPi where

  module _ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') (SqFillB : (x : A) → SqFill {ℓ = ℓ'} (B x)) where
    SqFillPiAB : SqFill {ℓ = ℓ ⊔ ℓ'} ((a : A) → B a)
    SqFillPiAB {lu} {ld} l {ru} {rd} r u d i j a =
        SqFillB a {lu a} {ld a} (λ i → l i a) {ru a} {rd a} (λ i → r i a) (λ i → u i a) (λ i → d i a) i j

  {-# BUILTIN SQFILLPI SqFillPiAB #-}
