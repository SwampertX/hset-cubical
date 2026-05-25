-- trying to recreate myst

{-# OPTIONS --cubical #-}

open import Agda.Builtin.Sigma
open import Agda.Builtin.Cubical.Path
open import Agda.Primitive
open import Agda.Primitive.Cubical

-- pointed types
Type∙ : ∀{ℓ} → Set (lsuc ℓ)
Type∙ {ℓ} = Σ (Set ℓ) (λ A → A)
-- the path space of pointed types is a prop (?)
pathTo : ∀{ℓ} → Type∙ {ℓ} → Set (lsuc ℓ)
pathTo X∙ = Σ Type∙ (λ Y∙ → X∙ ≡ Y∙)

isProp : ∀{ℓ} → Set ℓ → Set ℓ
isProp A = {a b : A} → a ≡ b

-- actually contractible to (X , x).
isPropPathTo : ∀{ℓ} (X∙ : Type∙ {ℓ}) → isProp (pathTo X∙)
isPropPathTo (X , x) {A∙ , eqa} {B∙ , eqb} i .fst = {!λ j → eqa (~ j)!}
isPropPathTo (X , x) {A∙ , eqa} {B∙ , eqb} i .snd = {!!}

-- prop truncation
data ∥_∥ {ℓ} (X : Set ℓ) : Set ℓ where
  ∣_∣ : X → ∥ X ∥
  trunc : isProp ∥ X ∥

-- rec of prop truncation
∥-rec : ∀{ℓ} {X : Set ℓ} (P : ∥ X ∥ → Set ℓ) (P∣_∣ : (x : X) → P ∣ x ∣) (Ptrunc : (x' : ∥ X ∥) → isProp (P x')) (x : ∥ X ∥) → P x
∥-rec P P∣_∣ Ptrunc ∣ x ∣ = P∣ x ∣
-- ∥-rec P P∣_∣ Ptrunc (trunc {a} {b} i) = {! Ptrunc {a = ∥-rec P P∣_∣ Ptrunc a}(trunc i) i !}

-- try to map from truncation back
