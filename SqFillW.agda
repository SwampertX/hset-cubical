{-# OPTIONS --cubical=no-glue #-}

open import SqFillDef
open import Helper

module SqFillW where
  module _ (S : Type) (P : S → Type) (SqFillS : SqFill S) (SqFillP : (s : S) → SqFill (P s)) where

    open import Agda.Builtin.Bool
    open import Agda.Builtin.Nat renaming (Nat to ℕ)
    open import Agda.Builtin.Sigma

    data W (S : Type) (P : S → Type) : Type where
        sup-W : (s : S) → (P s → W S P) → W S P

    NatW : Type
    NatW = W Bool λ { true → ⊥ ; false → ⊤}


    Nat→NatW : ℕ → NatW
    Nat→NatW zero = sup-W true (λ ())
    Nat→NatW (suc n) = sup-W false (λ tt → Nat→NatW n)

    NatW→Nat : NatW → ℕ
    NatW→Nat (sup-W true x) = zero
    NatW→Nat (sup-W false x) = suc (NatW→Nat (x tt))

    invℕ : (n : ℕ) → NatW→Nat (Nat→NatW n) ≡ n
    invℕ zero = refl
    invℕ (suc n) = cong suc (invℕ n)

    invNatW : (x : NatW) → Nat→NatW (NatW→Nat x) ≡ x
    invNatW (sup-W true x) = cong (sup-W true) {!!}
    invNatW (sup-W false x) = cong (sup-W false) {!λ i tt → invNatW (x tt)!}

    doubleW : NatW → NatW
    doubleW (sup-W true x) = sup-W true x
    doubleW (sup-W false x) = sup-W false (λ _ → sup-W false (λ _ → sup-W true λ ()))

    W-elim : ∀ {S P} → (B : W S P → Type) → (Bsup-W : (s : S) → (f : P s → W S P) → B (sup-W s f)) → (w : W S P) → B w
    W-elim {S} {P} B Bsup-W (sup-W s x) = Bsup-W s x


    CoverW : (x y : W S P) → Type
    CoverW (sup-W s x) (sup-W s' x') = Σ (s ≡ s') (λ p → PathP (λ i → (P (p i) → W S P)) x x')

    reflCodeW : {x : W S P} → CoverW x x
    reflCodeW {sup-W s x} = refl , refl

    encodeW : {x y : W S P} → x ≡ y → CoverW x y
    encodeW {x} p = transport (λ i → CoverW x (p i)) reflCodeW

    encodeReflW : {x : W S P} → encodeW (refl {x = x}) ≡ reflCodeW {x = x}
    encodeReflW {x = sup-W s x} i .fst = transp (λ _ → s ≡ s) i refl
    encodeReflW {x = sup-W s x} i .snd = λ j z → {!!}
      -- transp (λ j → PathP (λ k → P (encodeReflW {x = sup-W s x} i .fst k) → W S P) x x) i
      --        (λ j → {!transp (λ k → P (encodeReflW {x = sup-W s x} i .fst j) → W S P) (((~ j) ∨ j) ∨ i) x!})

    decodeW : {x y : W S P} → CoverW x y → x ≡ y
    decodeW {x = sup-W s x} {y = sup-W s' x'} (ps , px) = {! cong₂ sup-W ps px !}

    encodeDecodeW : (x y : W S P) → (c : CoverW x y) → encodeW (decodeW c) ≡ c
    encodeDecodeW (sup-W s x) (sup-W s' x') (ps , px) i .fst = {!transp (λ _ → s ≡ (ps i)) i !}
    encodeDecodeW (sup-W s x) (sup-W s' x') (ps , px) i .snd = {!!}

    -- open import Cubical.Foundations.Prelude using (cong₂)
    -- decodeEncodeW : {x y : W S P} → (p : x ≡ y) → decodeW (encodeW p) ≡ p
    -- decodeEncodeW {sup-W s x} {y} =
    --   J (λ y p → decodeW (encodeW p) ≡ p)
    --     -- (λ i → cong₂ sup-W (transportRefl (refl {x = s}) i) λ j → transportRefl {!!} i)
    --     (λ i → cong₂ sup-W (transp (λ _ → s ≡ s) i (refl {x = s})) (transp (λ _ → PathP {!λ i → P (transportRefl s i) → W S P!} x x) i (refl {x = x})))
    --     -- {!cong (cong₂ sup-W) (transportRefl ?)!}
    --     {y}

    -- SqFillW : SqFill (W S P)
    -- SqFillW {sup-W slu xlu} {sup-W sld xld} l {sup-W sru xru} {sup-W srd xrd} r u d i j =
    --     (hcomp (λ where
    --         k (i = i0) → decodeEncodeW l k j
    --         k (i = i1) → decodeEncodeW r k j
    --         k (j = i0) → decodeEncodeW u k i
    --         k (j = i1) → decodeEncodeW d k i)
    --     (sup-W (sqs i j) {!SqFillP (sqs i j) (encodeW)  !}))
    --     where
    --       SqFillPs→WSP : (s : S) → SqFill (P s → W S P)
    --       SqFillPs→WSP s = {!SqFillPiAB (P s) (λ _ → W S P) ()!}

    --       -- SqFillCoverW : (w : W S P) → SqFill (CoverW w w)
    --       -- SqFillCover (sup-W s x) = {! SqFillSigmaAB S SqFillS (λ s → (P s → W S P)) (λ s → SqFillPs→WSP s) !}

    --       sqs = SqFillS (encodeW l .fst) (encodeW r .fst) (encodeW u .fst) (encodeW d .fst)
    --   -- {!sup-W (SqFillS ? ? ? ? i j) ?!}
