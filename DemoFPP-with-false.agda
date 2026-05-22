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
open import SqFill using (SqFill)

data ⊥ : Set where

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

refl : ∀ {ℓ} {A : Set ℓ} {a : A} → a ≡ a
refl {a = a} = λ _ → a

primitive prim^sqFill : (A : Set) → SqFill A

tm-sqFill : SqFill ty
tm-sqFill = prim^sqFill ty

tm-uip : (tm1 tm2 : ty) (p q : tm1 ≡ tm2) → p ≡ q
tm-uip tm1 tm2 p q = tm-sqFill p q refl refl

tm-true-sq-is-refl : tm-sqFill {tm-true} refl refl refl refl ≡ refl
tm-true-sq-is-refl = refl

postulate decEqNat : ((a b : ℕ) → (a ≡ b) ⊎ (a ≡ b → ⊥))

tm-false : ty
tm-false .fst = false
tm-false .snd = just decEqNat

-- computes, but irregular
tm-false-sq-is-refl : tm-sqFill {tm-false} refl refl refl refl ≡ refl
tm-false-sq-is-refl = refl
