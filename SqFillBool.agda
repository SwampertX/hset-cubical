{-# OPTIONS --cubical=no-glue #-}

open import Helper
open import Agda.Builtin.Bool

module SqFillBool where
  true≠false : true ≡ false → ⊥
  true≠false p = transport (cong isTrue p) true
    where
      isTrue : Bool → Type
      isTrue true = Bool
      isTrue false = ⊥

  K-Bool : (P : {b : Bool} → b ≡ b → Type)
      → (∀{b} → P {b} refl)
      → ∀{b} → (q : b ≡ b) → P q
  K-Bool P Pr {false} = J (λ{ false q → P q ; true _ → ⊥ }) Pr
  K-Bool P Pr {true}  = J (λ{ true q → P q ; false _ → ⊥ }) Pr

  KBool : {b : Bool} → (p : b ≡ b) → p ≡ refl
  KBool {true} = J (λ{ true q → q ≡ refl ; false _ → ⊥ }) refl
  KBool {false} = J (λ{ false q → q ≡ refl ; true _ → ⊥ }) refl

  -- it's also possible to implement this term by inspecting the paths instead
  -- then sqfill refl refl refl refl would definitionally to our term
  -- but right now it doesn't (Jrefl is not definitional)
  SqFillBool : SqFill Bool
  SqFillBool {true} {true} l {true} {true} r u d i j =
    (hcomp (λ where k (i = i0) → KBool l (~ k) j
                    k (i = i1) → KBool r (~ k) j
                    k (j = i0) → KBool u (~ k) i
                    k (j = i1) → KBool d (~ k) i) true)
  SqFillBool {false} {false} l {false} {false} r u d i j =
    (hcomp (λ where k (i = i0) → KBool l (~ k) j
                    k (i = i1) → KBool r (~ k) j
                    k (j = i0) → KBool u (~ k) i
                    k (j = i1) → KBool d (~ k) i) false)
  SqFillBool {true} {false} l _ _ _ = ⊥-elim (true≠false l)
  SqFillBool {true} {true} _ {false} _ u _ = ⊥-elim (true≠false u)
  SqFillBool {true} {true} _ {true} {false} _ _ d = ⊥-elim (true≠false d)
  SqFillBool {false} {true} l _ _ _ = ⊥-elim (true≠false (sym l))
  SqFillBool {false} {false} _ {true} _ u _ = ⊥-elim (true≠false (sym u))
  SqFillBool {false} {false} _ {false} {true} _ _ d = ⊥-elim (true≠false (sym d))

  {-# BUILTIN SQFILLBOOL SqFillBool #-}
