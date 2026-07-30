{-# OPTIONS --cubical=no-glue #-}

open import Helper
open import SqFillDef

module SqFillUnit where
  SqFillUnit : SqFill ⊤
  SqFillUnit {tt} {tt} l {tt} {tt} r u d i j =
      hcomp (λ k → λ {(i = i0) → isProp⊤ tt (l j) k
                    ; (i = i1) → isProp⊤ tt (r j) k
                    ; (j = i0) → isProp⊤ tt (u i) k
                    ; (j = i1) → isProp⊤ tt (d i) k}) tt
    where
      isProp⊤ : (a b : ⊤) → a ≡ b
      isProp⊤ tt tt _ = tt

  {-# BUILTIN SQFILLUNIT SqFillUnit #-}
