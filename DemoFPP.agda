{-# OPTIONS --cubical=uip #-}

open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Sigma
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Product
open import Agda.Builtin.Coproduct
open import SqFillDef using (SqFill)

data ⊥ : Set where

refl : ∀ {ℓ} {A : Set ℓ} {a : A} → a ≡ a
refl {a = a} = λ _ → a

ty : Set
ty = Σ Bool (λ{
       true → List (List (ℕ × ℕ));
       false → Maybe((a b : ℕ) → (a ≡ b) ⊎ (a ≡ b → ⊥))
     })

tm-true : ty
tm-true .fst = true
tm-true .snd = ns ∷ ns ∷ []
  where
  ns : List (ℕ × ℕ)
  ns = ((1 , 2) ∷ (3 , 4) ∷ [])

primitive prim^sqFill : (A : Set) → SqFill A

tm-true-sq-is-refl : prim^sqFill ty {tm-true} refl refl refl refl ≡ refl
tm-true-sq-is-refl = refl
