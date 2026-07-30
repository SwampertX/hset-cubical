-- If you are running mainline Agda, use --cubical
{-# OPTIONS --cubical=no-glue --guardedness #-}

-- Prelude is glue-free: --cubical=no-glue works out of the box.
open import Cubical.Foundations.Prelude
  using (
    Level; Type; _≡_; refl; Square;
    I; _∧_; _∨_; ~_; i0; i1;
    Σ-syntax; fst; snd;
    cong; transport; PathP; transp; transport-filler; comp; Partial; _[_↦_]; inS; outS; hcomp;
    isProp; J; transportRefl; sym; toPathP
  )

open import SqFillDef using (SqFill)

SqFill-lr→ud : {A : Type}
  {lu ld : A} (l : lu ≡ ld)
  {ru rd : A} (r : ru ≡ rd)
  (u : lu ≡ ru) (d : ld ≡ rd)
  → (lr : PathP (λ i → u i ≡ d i) l r)
  → PathP (λ j → l j ≡ r j) u d
SqFill-lr→ud l r u d lr i j = lr j i

SqFill-lr→rl : {A : Type}
  {lu ld : A} (l : lu ≡ ld)
  {ru rd : A} (r : ru ≡ rd)
  (u : lu ≡ ru) (d : ld ≡ rd)
  → (lr : PathP (λ i → u i ≡ d i) l r)
  → PathP (λ i → u (~ i) ≡ d (~ i)) r l
SqFill-lr→rl l r u d lr i j = lr (~ i) j

SqFill-ud→du : {A : Type}
  {lu ld : A} (l : lu ≡ ld)
  {ru rd : A} (r : ru ≡ rd)
  (u : lu ≡ ru) (d : ld ≡ rd)
  → (ud : PathP (λ j → l j ≡ r j) u d)
  → PathP (λ j → l (~ j) ≡ r (~ j)) d u
SqFill-ud→du l r u d ud i j = ud (~ i) j
