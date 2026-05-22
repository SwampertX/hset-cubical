{-# OPTIONS --without-K #-}

module _ where

open import Data.Fin hiding (_+_)
open import Data.Nat
open import Data.Sum
open import Relation.Binary.PropositionalEquality

record _≅_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
    from-to : (x : A) → from (to x) ≡ x
    to-from : (y : B) → to (from y) ≡ y
open _≅_

insert-element-left : {m n : ℕ} → Fin m ⊎ Fin n → Fin (suc m) ⊎ Fin n
insert-element-left (inj₁ y) = inj₁ (suc y)
insert-element-left (inj₂ y) = inj₂ y

iso : (m n : ℕ) → (Fin m ⊎ Fin n) ≅ Fin (m + n)
iso 0 n .to (inj₁ ())
iso 0 n .to (inj₂ x) = x
iso 0 n .from x = inj₂ x
iso 0 n .from-to (inj₁ ())
iso 0 n .from-to (inj₂ x) = refl
iso 0 n .to-from x = refl
iso (suc m) n .to (inj₁ zero) = zero
iso (suc m) n .to (inj₁ (suc x)) = suc (iso m n .to (inj₁ x))
iso (suc m) n .to (inj₂ x) = suc (iso m n .to (inj₂ x))
iso (suc m) n .from zero = inj₁ zero
iso (suc m) n .from (suc x) = insert-element-left (iso m n .from x)
iso (suc m) n .from-to (inj₁ zero) = refl
iso (suc m) n .from-to (inj₁ (suc x)) = cong insert-element-left (iso m n .from-to (inj₁ x))
iso (suc m) n .from-to (inj₂ x) = cong insert-element-left (iso m n .from-to (inj₂ x))
iso (suc m) n .to-from zero = refl
iso (suc m) n .to-from (suc x) with iso m n .from x in e
iso (suc m) n .to-from (suc x) | inj₁ y = trans (cong (λ z → suc (iso m n .to z)) (sym e)) (cong suc (iso m n .to-from x))
-- We want: iso (suc m) n .to (iso (suc m) n .from (suc x)) ≡ suc x
-- i.e. iso (suc m) n .to (insert-element-left (iso m n .from x)) ≡ suc x
-- After with-abstraction, we have
-- e : iso m n .from x ≡ inj₂ y
-- and we want:
-- iso (suc m) n .to (insert-element-left (inj₂ y)) ≡ suc x
-- i.e. iso (suc m) n .to (inj₂ y) ≡ suc x
-- i.e. suc (iso m n .to (inj₂ y)) ≡ suc x
-- This holds since
-- suc (iso m n .to (inj₂ y))
-- ≡ suc (iso m n .to (iso m n .from x)) [by e]
-- ≡ suc (x) [by iso m n .to-from x]
iso (suc m) n .to-from (suc x) | inj₂ y = trans (cong (λ z → suc (iso m n .to z)) (sym e)) (cong suc (iso m n .to-from x))
