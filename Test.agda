{-# OPTIONS --cubical=no-glue --guardedness #-}

open import Agda.Primitive using (Level) renaming (Set to Type)
open import Agda.Primitive.Cubical public
  renaming ( primIMin       to _∧_  -- I → I → I
           ; primIMax       to _∨_  -- I → I → I
           ; primINeg       to ~_   -- I → I
           ; isOneEmpty     to empty
           ; primComp       to comp
           ; primHComp      to hcomp
           ; primTransp     to transp
           ; itIsOne        to 1=1 )
open import Agda.Primitive.Cubical public
open import Agda.Builtin.Cubical.Path public

-- primitive primIMin : I → I → I
primitive
  primSqFill : {ℓ : Level} (A : I → I → Type ℓ)
    {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
    {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
    (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
    → PathP (λ i → PathP (λ j → A i j) (a₋₀ i) (a₋₁ i)) a₀₋ a₁₋

sqFill = primSqFill

module hello (A B : Type) where
  open import SqPFill renaming (SqPFill to SqFill)
  p : SqFill (λ i j → A → B)
  p =  sqFill (λ i j → A → B) 

  p' : p ≡ {!!}
  p' _ = p
