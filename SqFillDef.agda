{-# OPTIONS  --cubical=no-glue #-}

module SqFillDef where
  open import Agda.Primitive public renaming (Set   to Type)
  open import Agda.Builtin.Cubical.Path public
 -- SqFill : Type → Type
  SqFill : ∀{ℓ} → Type ℓ → Type ℓ
  SqFill A =
    {a₀₀ : A} {a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
    {a₁₀ : A} {a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
    (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
    → PathP (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋

  {-# BUILTIN SQFILL SqFill #-}
