{-# OPTIONS --injective-type-constructors #-}

open import Agda.Builtin.Product
open import Agda.Builtin.Equality

data test : Set → Set where

data ⊥ : Set where

data ⊤ : Set where
  tt : ⊤

eq : ∀ {A B} → test A ≡ test B → A ≡ B
eq refl = refl

-- absurd : ⊤ ≡ ⊥
-- absurd = eq {A = ⊤} {B = ⊥} {!!}
