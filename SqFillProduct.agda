{-# OPTIONS --cubical=no-glue #-}

open import Helper
open import Agda.Builtin.Product

module SqFillProduct where
  module _ {ℓ ℓ'} (A : Type ℓ) (SqFillA : SqFill A) (B : Type ℓ') (SqFillB : SqFill B) where
    SqFillProduct : SqFill (A × B)
    SqFillProduct {lu} {ld} l {ru} {rd} r u d i j .fst = SqFillA (cong fst l) (cong fst r) (cong fst u) (cong fst d) i j
    SqFillProduct {lu} {ld} l {ru} {rd} r u d i j .snd = SqFillB (cong snd l) (cong snd r) (cong snd u) (cong snd d) i j

  {-# BUILTIN SQFILLPRODUCT SqFillProduct #-}
