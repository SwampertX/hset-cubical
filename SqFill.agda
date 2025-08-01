{-# OPTIONS --cubical --type-in-type #-} -- the "normal" cubical agda

-- TODO: clean up imports to convince others we did not use Glue!
open import Cubical.Foundations.Prelude
  using (
    Level; Type; _≡_; refl; Square;
    I; _∧_; _∨_; ~_; i0; i1;
    Σ-syntax; fst; snd;
    cong; transport; PathP; transp; transport-filler; comp; Partial; _[_↦_]; inS; outS; hcomp;
    isProp; fromPathP; J; transportRefl; sym
  )

module SqFill where
  hSqFill : {ℓ : Level} → (A : Type ℓ) → Type ℓ
  hSqFill A =
    {a₀₀ : A} {a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
    {a₁₀ : A} {a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
    (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
    → Square a₀₋ a₁₋ a₋₀ a₋₁

  private postulate
    A A' : Type
    hSqFillA : hSqFill A
    hSqFillA' : hSqFill A'
    B : A → Type
    hSqFillB : (x : A) → hSqFill (B x)

  hSqFillPiAB : hSqFill ((a : A) → B a)
  hSqFillPiAB l r u d i j a = hSqFillB a (λ i → l i a) (λ i → r i a) (λ i → u i a) (λ i → d i a) i j

  if_then_else_end : I → I → I → I
  if i then j else k end = (k ∧ (~ i ∨ j)) ∨ (i ∧ j)

  {-# INLINE if_then_else_end #-}

  sqfillSigmaAB : hSqFill (Σ[ a ∈ A ] B a)
  sqfillSigmaAB l r u d i j .fst = hSqFillA (cong fst l) (cong fst r) (cong fst u) (cong fst d) i j
  sqfillSigmaAB {lu} {ld} l {ru} {rd} r u d i j .snd = outS (sqb i j)
    where
      sqa : Square (cong fst l) (cong fst r) (cong fst u) (cong fst d)
      sqa = hSqFillA (cong fst l) (cong fst r) (cong fst u) (cong fst d)

      spread : (i j i' j' : I) → sqa i j ≡ sqa i' j'
      spread i j i' j' k = sqa (if k then i' else i end) (if k then j' else j end)

      lub : B (sqa i0 i0)
      lub = snd lu
      lub' : B (sqa i j)
      lub' = transport (λ k → B (spread i0 i0 i j k)) lub
      LemmaLU : PathP (λ k → B (spread i0 i0 i j k)) lub lub'
      LemmaLU k = transp (λ l → B (spread i0 i0 i j (k ∧ l))) (~ k) lub

      ldb : B (fst ld)
      ldb = snd ld
      ldb' : B (sqa i j)
      ldb' = transport (λ k → B (spread i0 i1 i j k)) ldb
      LemmaLD : PathP (λ k → B (spread i0 i1 i j k)) ldb ldb'
      LemmaLD k = transp (λ l → B (spread i0 i1 i j (k ∧ l))) (~ k) ldb

      lb : PathP (λ k → B (spread i0 i0 i0 i1 k)) lub ldb
      lb = cong snd l
      lb' : PathP (λ k → B (spread i j i j k)) lub' ldb'
      lb' j' = comp (λ k → B (spread (k ∧ i) (k ∧ j) (k ∧ i) (~ k ∨ j) j'))
                    (λ where
                      k (j' = i0) → LemmaLU k
                      k (j' = i1) → LemmaLD k) (lb j')
      LemmaL : PathP (λ k' → PathP (λ k → B (spread (k' ∧ i) (k' ∧ j) (k' ∧ i) (~ k' ∨ j) k)) (LemmaLU k') (LemmaLD k')) lb lb'
      LemmaL k' = transport-filler (λ k' → PathP (λ k → B (spread (k' ∧ i) (k' ∧ j) (k' ∧ i) (~ k' ∨ j) k)) (LemmaLU k') (LemmaLD k')) lb k'

      rub : B (fst ru)
      rub = snd ru
      rub' : B (sqa i j)
      rub' = transport (λ k → B (spread i1 i0 i j k)) rub
      LemmaRU : PathP (λ k → B (spread i1 i0 i j k)) rub rub'
      LemmaRU k = transp (λ l → B (spread i1 i0 i j (k ∧ l))) (~ k) rub

      rdb : B (fst rd)
      rdb = snd rd
      rdb' : B (sqa i j)
      rdb' = transport (λ k → B (spread i1 i1 i j k)) rdb
      LemmaRD : PathP (λ k → B (spread i1 i1 i j k)) rdb rdb'
      LemmaRD k = transp (λ l → B (spread i1 i1 i j (k ∧ l))) (~ k) rdb

      rb : PathP (λ j → B (sqa i1 j)) rub rdb
      rb = cong snd r
      rb' : rub' ≡ rdb'
      rb' j' = comp (λ k → B (spread (~ k ∨ i) (k ∧ j) (~ k ∨ i) (~ k ∨ j) j'))
                    (λ where
                      k (j' = i0) → LemmaRU k
                      k (j' = i1) → LemmaRD k) (rb j')
      LemmaR : PathP (λ k' → PathP (λ k → B (spread (~ k' ∨ i) (k' ∧ j) (~ k' ∨ i) (~ k' ∨ j) k)) (LemmaRU k') (LemmaRD k')) rb rb'
      LemmaR k' = transport-filler (λ k' → PathP (λ k → B (spread (~ k' ∨ i) (k' ∧ j) (~ k' ∨ i) (~ k' ∨ j) k)) (LemmaRU k') (LemmaRD k')) rb k'

      ub : PathP (λ i → B (sqa i i0)) lub rub
      ub = cong snd u
      ub' : lub' ≡ rub'
      ub' i' = comp (λ k → B (spread (k ∧ i) (k ∧ j) (~ k ∨ i) (k ∧ j) i'))
                    (λ where
                      k (i' = i0) → LemmaLU k
                      k (i' = i1) → LemmaRU k) (ub i')
      LemmaU : PathP (λ k' → PathP (λ k → B (spread (k' ∧ i) (k' ∧ j) (~ k' ∨ i) (k' ∧ j) k)) (LemmaLU k') (LemmaRU k')) ub ub'
      LemmaU k' = transport-filler (λ k' → PathP (λ k → B (spread (k' ∧ i) (k' ∧ j) (~ k' ∨ i) (k' ∧ j) k)) (LemmaLU k') (LemmaRU k')) ub k'

      db : PathP (λ i → B (sqa i i1)) ldb rdb
      db = cong snd d
      db' : ldb' ≡ rdb'
      db' i' = comp (λ k → B (spread (k ∧ i) (~ k ∨ j) (~ k ∨ i) (~ k ∨ j) i'))
                    (λ where
                      k (i' = i0) → LemmaLD k
                      k (i' = i1) → LemmaRD k) (db i')
      LemmaD : PathP (λ k' → PathP (λ k → B (spread (k' ∧ i) (~ k' ∨ j) (~ k' ∨ i) (~ k' ∨ j) k)) (LemmaLD k') (LemmaRD k')) db db'
      LemmaD k' = transport-filler (λ k' → PathP (λ k → B (spread (k' ∧ i) (~ k' ∨ j) (~ k' ∨ i) (~ k' ∨ j) k)) (LemmaLD k') (LemmaRD k')) db k'

      sqb-hollow : (i' j' : I) → Partial (i' ∨ j' ∨ ~ i' ∨ ~ j') (B (sqa i' j'))
      sqb-hollow i' j' (i' = i0) = l j' .snd
      sqb-hollow i' j' (i' = i1) = r j' .snd
      sqb-hollow i' j' (j' = i0) = u i' .snd
      sqb-hollow i' j' (j' = i1) = d i' .snd

      sqb'-hollow : (i' j' : I) → Partial (i' ∨ j' ∨ ~ i' ∨ ~ j') (B (sqa i j))
      sqb'-hollow i' j' (i' = i0) = lb' j'
      sqb'-hollow i' j' (i' = i1) = rb' j'
      sqb'-hollow i' j' (j' = i0) = ub' i'
      sqb'-hollow i' j' (j' = i1) = db' i'

      sqb' : (i' j' : I) → (B (sqa i j)) [ (i' ∨ j' ∨ ~ i' ∨ ~ j') ↦ sqb'-hollow i' j' ]
      sqb' i' j' = inS (hSqFillB (sqa i j) lb' rb' ub' db' i' j')

      sqb : (i' j' : I) → (B (sqa i' j')) [ ( i' ∨ ~ i' ∨ j' ∨ ~ j' ) ↦ sqb-hollow i' j' ]
      sqb i' j' = inS (comp (λ k → B (spread i j i' j' k)) (
                      λ where
                        k (i' = i0) → LemmaL (~ k) j'
                        k (i' = i1) → LemmaR (~ k) j'
                        k (j' = i0) → LemmaU (~ k) i'
                        k (j' = i1) → LemmaD (~ k) i') (outS (sqb' i' j')))

  sqfillSigmaAB' : hSqFill (Σ[ a ∈ A ] B a)
  sqfillSigmaAB' l r u d i j .fst = hSqFillA (cong fst l) (cong fst r) (cong fst u) (cong fst d) i j
  sqfillSigmaAB' {lu} {ld} l {ru} {rd} r u d i j .snd =
    pathToPathP (λ i → PathP (λ j → SqB i j) (u i .snd) (d i .snd)) (cong snd l) (cong snd r)
      (hSqFill→PathPIsProp (λ j → SqB i1 j) (hSqFillB (sqA i1 i1)) (snd ru) (snd rd) (transport (λ i → PathP (λ j → SqB i j) (u i .snd) (d i .snd)) (cong snd l)) (cong snd r) )
      i j
    where
      sqA : I → I → A
      sqA i j = (hSqFillA (cong fst l) (cong fst r) (cong fst u) (cong fst d) i j)

      SqB : I → I → Type
      SqB i j = B (sqA i j)

      -- the key idea is
      pathToPathP : (A : I → Type) (x : A i0) (y : A i1) → transport (λ i → A i) x ≡ y → PathP A x y
      pathToPathP A x y p i = hcomp (λ j → λ {
        (i = i0) → x;
        (i = i1) → p j
        }) (transp (λ j → A (i ∧ j)) (~ i) x)

      open import Cubical.Foundations.Isomorphism using (Iso)
      open import Cubical.Foundations.Path using (PathPIsoPath)
      open import Cubical.Foundations.HLevels using (isPropRetract)

      -- Kan operations hidden in:
      -- - isPropRetract has 1 hcomp
      -- - PathPIsoPath .Iso.leftInv needs uniqueness of hcomp, and also several hcomps
      hSqFill→PathPIsProp : (A : I → Type) (hSqFillA : hSqFill (A i1)) (x : A i0) (y : A i1) → isProp (PathP A x y)
      hSqFill→PathPIsProp A hSqFillA x y = isPropRetract fromPathP (pathToPathP A x y) (PathPIsoPath A x y .Iso.leftInv) (λ p q → hSqFillA p q refl refl)

  data _+_ (A B : Type) : Type where
    inl : A → A + B
    inr : B → A + B

  data ⊥ : Type where

  ⊥-elim : {A : Type} (x : ⊥) → A
  ⊥-elim ()

  data ⊤ : Type where
    tt : ⊤

  inl≠inr : {A B : Type} (x : A) (y : B) → (inl x ≡ inr y) → ⊥
  inl≠inr {A} {B} x y p = transport (cong isLeft p) tt
    where
      isLeft : (A + B) → Type
      isLeft (inl x) = ⊤
      isLeft (inr y) = ⊥

  Cover : {A B : Type} (c c' : A + B) → Type
  Cover (inl x) (inl y) = x ≡ y
  Cover (inr x) (inr y) = x ≡ y
  Cover _ _ = ⊥

  reflCode : {A B : Type} (c : A + B) → Cover c c
  reflCode (inl x) = refl
  reflCode (inr x) = refl

  encode : {A B : Type} {c c' : A + B} → c ≡ c' → Cover c c'
  encode {c = c} p = transport (λ i → Cover c (p i)) (reflCode c)

  decode : {A B : Type} {c c' : A + B} → Cover c c' → c ≡ c'
  decode {c = inl x} {c' = inl y} = cong inl
  decode {c = inr x} {c' = inr y} = cong inr

  decodeEncode : {A B : Type} {c c' : A + B} (p : c ≡ c') → decode (encode p) ≡ p
  decodeEncode {c = inl x} = J (λ c' p → decode (encode p) ≡ p) (cong (cong inl) (transportRefl refl))
  decodeEncode {c = inr x} = J (λ c' p → decode (encode p) ≡ p) (cong (cong inr) (transportRefl refl))

  hSqFillCoproduct : hSqFill (A + A')
  hSqFillCoproduct {inl lu} {inl ld} l {inl ru} {inl rd} r u d i j =
    (hcomp (λ where
        k (i = i0) → decodeEncode l k j
        k (i = i1) → decodeEncode r k j
        k (j = i0) → decodeEncode u k i
        k (j = i1) → decodeEncode d k i)
      (inl {A} {A'} (hSqFillA (encode l) (encode r) (encode u) (encode d) i j)))
  hSqFillCoproduct {inr lu} {inr ld} l {inr ru} {inr rd} r u d i j =
    (hcomp (λ where
        k (i = i0) → decodeEncode l k j
        k (i = i1) → decodeEncode r k j
        k (j = i0) → decodeEncode u k i
        k (j = i1) → decodeEncode d k i)
      (inr {A} {A'} (hSqFillA' (encode l) (encode r) (encode u) (encode d) i j)))
  hSqFillCoproduct {inl x} {inr y} l _ _ _ = ⊥-elim (inl≠inr x y l)
  hSqFillCoproduct {inr x} {inl y} l _ _ _ = ⊥-elim (inl≠inr y x (sym l))
  hSqFillCoproduct {inl x} {_} _ {inr y} _ u _ = ⊥-elim (inl≠inr x y u)
  hSqFillCoproduct {inr x} {_} _ {inl y} _ u _ = ⊥-elim (inl≠inr y x (sym u))
  hSqFillCoproduct {_} {inl x} _ {_} {inr y} _ _ d = ⊥-elim (inl≠inr x y d)
  hSqFillCoproduct {_} {inr x} _ {_} {inl y} _ _ d = ⊥-elim (inl≠inr y x (sym d))
  -- hSqFillCoproduct {_} {_} _ {inl x} {inr y} r _ _ = ⊥-elim (inl≠inr x y r)
  -- hSqFillCoproduct {_} {_} _ {inr x} {inl y} r _ _ = ⊥-elim (inl≠inr y x (sym r))

  hSqFillPath : {a b : A} → hSqFill (a ≡ b)
  hSqFillPath {_} {_} {lu} l r u d i j =
    hcomp (λ k → λ { (i = i0) → hSqFillA lu (l j) refl refl k
                  ; (i = i1) → hSqFillA lu (r j) refl refl k
                  ; (j = i0) → hSqFillA lu (u i) refl refl k
                  ; (j = i1) → hSqFillA lu (d i) refl refl k}) lu
