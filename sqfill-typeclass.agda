{-# OPTIONS --cubical=uip #-}
module sqfill-typeclass where

open import SqFill

record SqFillTC (A : Set) : Set where
  constructor sqfill-instance
  field
    sqfill : SqFill A

instance
  sqfill-pi-instance : {A : Set} → {B : A → Set} → ⦃ ∀ {a : A} → SqFillTC (B a) ⦄ → SqFillTC ((a : A) → B a)
  sqfill-pi-instance {A} {B} .SqFillTC.sqfill = SqFillPi.SqFillPiAB A B λ x {a₀₀ = a₁} {a₀₁ = a₂} a₀₋ {a₁₀} {a₁₁} a₁₋ a₋₀ a₋₁ →
                                                                           _ .SqFillTC.sqfill a₀₋ a₁₋ (λ i → a₋₀ i) (λ i → a₋₁ i)
