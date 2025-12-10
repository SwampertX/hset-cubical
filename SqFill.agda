-- If you are running mainline Agda, use --cubical
{-# OPTIONS --cubical=no-glue #-}

open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical
  renaming ( primIMin       to _∧_  -- I → I → I
           ; primIMax       to _∨_  -- I → I → I
           ; primINeg       to ~_   -- I → I
           ; primComp       to comp
           ; primHComp      to hcomp
           ; primTransp     to transp)

open import Agda.Primitive renaming (Set   to Type)
open import Agda.Builtin.Sigma
open import Agda.Builtin.Cubical.Sub
  renaming (primSubOut to outS)


module SqFill where
  -- SqFill : {ℓ : Level} → (A : Type ℓ) → Type ℓ
  -- SqFill A =
  --   {a₀₀ : A} {a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
  --   {a₁₀ : A} {a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
  --   (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
  --   → PathP (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋
  SqFill : (A : Type) → Type
  SqFill A =
    {a₀₀ : A} {a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
    {a₁₀ : A} {a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
    (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
    → PathP (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋
  -- postulate SqFill : Type

  {-# BUILTIN SQFILL SqFill #-}

  open import Helper

  module SqFillPi (A : Type) (B : A → Type) (SqFillB : (x : A) → SqFill (B x)) where

    SqFillPiAB : SqFill ((a : A) → B a)
    SqFillPiAB {lu} {ld} l {ru} {rd} r u d i j a = SqFillB a {lu a} {ld a} (λ i → l i a) {ru a} {rd a} (λ i → r i a) (λ i → u i a) (λ i → d i a) i j

  {-# BUILTIN SQFILLPI SqFillPi.SqFillPiAB #-}

    -- data Unit : Type where
    --   tt : Unit

    -- postulate SqFillPiAB : SqFill Unit

  -- SqFillPiAB : (A : Type) (B : A → Type) (SqFillB : (x : A) → SqFill (B x)) → SqFill ((a : A) → B a)
  -- SqFillPiAB A B SqFillB lu ld l ru rd r u d i j a = SqFillB a (lu a) (ld a) (λ i → l i a) (ru a) (rd a) (λ i → r i a) (λ i → u i a) (λ i → d i a) i j
  -- {-# BUILTIN SQFILLPI SqFillPiAB #-}

  -- SqFillPiAB : (A : Type) (B : A → Type) (SqFillB : (x : A) → SqFill (B x)) → SqFill ((a : A) → B a)
  -- SqFillPiAB A B SqFillB {lu} {ld} l {ru} {rd} r u d i j a = SqFillB a {lu a} {ld a} (λ i → l i a) {ru a} {rd a} (λ i → r i a) (λ i → u i a) (λ i → d i a) i j
  -- {-# BUILTIN SQFILLPI SqFillPiAB #-}


  -- if_then_else_end : I → I → I → I
  -- if i then j else k end = (k ∧ (~ i ∨ j)) ∨ ((i ∨ k) ∧ j)

  -- {-# INLINE if_then_else_end #-}

  -- module SqFillSigma (A : Type) (SqFillA : SqFill A) (B : A → Type) (SqFillB : (x : A) → SqFill (B x)) where

  --   SqFillSigmaAB : SqFill (Σ A (λ a → B a))
  --   SqFillSigmaAB l r u d i j .fst = SqFillA (cong fst l) (cong fst r) (cong fst u) (cong fst d) i j
  --   SqFillSigmaAB {lu} {ld} l {ru} {rd} r u d i j .snd = outS (sqb i j)
  --       where
  --       sqa : Square (cong fst l) (cong fst r) (cong fst u) (cong fst d)
  --       sqa = SqFillA (cong fst l) (cong fst r) (cong fst u) (cong fst d)

  --       spread : (i j i' j' : I) → sqa i j ≡ sqa i' j'
  --       spread i j i' j' k = sqa (if k then i' else i end) (if k then j' else j end)

  --       lub : B (sqa i0 i0)
  --       lub = snd lu
  --       lub' : B (sqa i j)
  --       lub' = transport (λ k → B (spread i0 i0 i j k)) lub
  --       LemmaLU : PathP (λ k → B (spread i0 i0 i j k)) lub lub'
  --       LemmaLU k = transp (λ l → B (spread i0 i0 i j (k ∧ l))) (~ k) lub

  --       ldb : B (fst ld)
  --       ldb = snd ld
  --       ldb' : B (sqa i j)
  --       ldb' = transport (λ k → B (spread i0 i1 i j k)) ldb
  --       LemmaLD : PathP (λ k → B (spread i0 i1 i j k)) ldb ldb'
  --       LemmaLD k = transp (λ l → B (spread i0 i1 i j (k ∧ l))) (~ k) ldb

  --       lb : PathP (λ k → B (spread i0 i0 i0 i1 k)) lub ldb
  --       lb = cong snd l
  --       lb' : PathP (λ k → B (spread i j i j k)) lub' ldb'
  --       lb' j' = comp (λ k → B (spread (k ∧ i) (k ∧ j) (k ∧ i) (~ k ∨ j) j'))
  --                       (λ where
  --                       k (j' = i0) → LemmaLU k
  --                       k (j' = i1) → LemmaLD k) (lb j')
  --       LemmaL : PathP (λ k' → PathP (λ k → B (spread (k' ∧ i) (k' ∧ j) (k' ∧ i) (~ k' ∨ j) k)) (LemmaLU k') (LemmaLD k')) lb lb'
  --       LemmaL k' = transport-filler (λ k' → PathP (λ k → B (spread (k' ∧ i) (k' ∧ j) (k' ∧ i) (~ k' ∨ j) k)) (LemmaLU k') (LemmaLD k')) lb k'

  --       rub : B (fst ru)
  --       rub = snd ru
  --       rub' : B (sqa i j)
  --       rub' = transport (λ k → B (spread i1 i0 i j k)) rub
  --       LemmaRU : PathP (λ k → B (spread i1 i0 i j k)) rub rub'
  --       LemmaRU k = transp (λ l → B (spread i1 i0 i j (k ∧ l))) (~ k) rub

  --       rdb : B (fst rd)
  --       rdb = snd rd
  --       rdb' : B (sqa i j)
  --       rdb' = transport (λ k → B (spread i1 i1 i j k)) rdb
  --       LemmaRD : PathP (λ k → B (spread i1 i1 i j k)) rdb rdb'
  --       LemmaRD k = transp (λ l → B (spread i1 i1 i j (k ∧ l))) (~ k) rdb

  --       rb : PathP (λ j → B (sqa i1 j)) rub rdb
  --       rb = cong snd r
  --       rb' : rub' ≡ rdb'
  --       rb' j' = comp (λ k → B (spread (~ k ∨ i) (k ∧ j) (~ k ∨ i) (~ k ∨ j) j'))
  --                       (λ where
  --                       k (j' = i0) → LemmaRU k
  --                       k (j' = i1) → LemmaRD k) (rb j')
  --       LemmaR : PathP (λ k' → PathP (λ k → B (spread (~ k' ∨ i) (k' ∧ j) (~ k' ∨ i) (~ k' ∨ j) k)) (LemmaRU k') (LemmaRD k')) rb rb'
  --       LemmaR k' = transport-filler (λ k' → PathP (λ k → B (spread (~ k' ∨ i) (k' ∧ j) (~ k' ∨ i) (~ k' ∨ j) k)) (LemmaRU k') (LemmaRD k')) rb k'

  --       ub : PathP (λ i → B (sqa i i0)) lub rub
  --       ub = cong snd u
  --       ub' : lub' ≡ rub'
  --       ub' i' = comp (λ k → B (spread (k ∧ i) (k ∧ j) (~ k ∨ i) (k ∧ j) i'))
  --                       (λ where
  --                       k (i' = i0) → LemmaLU k
  --                       k (i' = i1) → LemmaRU k) (ub i')
  --       LemmaU : PathP (λ k' → PathP (λ k → B (spread (k' ∧ i) (k' ∧ j) (~ k' ∨ i) (k' ∧ j) k)) (LemmaLU k') (LemmaRU k')) ub ub'
  --       LemmaU k' = transport-filler (λ k' → PathP (λ k → B (spread (k' ∧ i) (k' ∧ j) (~ k' ∨ i) (k' ∧ j) k)) (LemmaLU k') (LemmaRU k')) ub k'

  --       db : PathP (λ i → B (sqa i i1)) ldb rdb
  --       db = cong snd d
  --       db' : ldb' ≡ rdb'
  --       db' i' = comp (λ k → B (spread (k ∧ i) (~ k ∨ j) (~ k ∨ i) (~ k ∨ j) i'))
  --                       (λ where
  --                       k (i' = i0) → LemmaLD k
  --                       k (i' = i1) → LemmaRD k) (db i')
  --       LemmaD : PathP (λ k' → PathP (λ k → B (spread (k' ∧ i) (~ k' ∨ j) (~ k' ∨ i) (~ k' ∨ j) k)) (LemmaLD k') (LemmaRD k')) db db'
  --       LemmaD k' = transport-filler (λ k' → PathP (λ k → B (spread (k' ∧ i) (~ k' ∨ j) (~ k' ∨ i) (~ k' ∨ j) k)) (LemmaLD k') (LemmaRD k')) db k'

  --       sqb-hollow : (i' j' : I) → Partial (i' ∨ j' ∨ ~ i' ∨ ~ j') (B (sqa i' j'))
  --       sqb-hollow i' j' (i' = i0) = l j' .snd
  --       sqb-hollow i' j' (i' = i1) = r j' .snd
  --       sqb-hollow i' j' (j' = i0) = u i' .snd
  --       sqb-hollow i' j' (j' = i1) = d i' .snd

  --       sqb'-hollow : (i' j' : I) → Partial (i' ∨ j' ∨ ~ i' ∨ ~ j') (B (sqa i j))
  --       sqb'-hollow i' j' (i' = i0) = lb' j'
  --       sqb'-hollow i' j' (i' = i1) = rb' j'
  --       sqb'-hollow i' j' (j' = i0) = ub' i'
  --       sqb'-hollow i' j' (j' = i1) = db' i'

  --       sqb' : (i' j' : I) → (B (sqa i j)) [ (i' ∨ j' ∨ ~ i' ∨ ~ j') ↦ sqb'-hollow i' j' ]
  --       sqb' i' j' = inS (SqFillB (sqa i j) lb' rb' ub' db' i' j')

  --       sqb : (i' j' : I) → (B (sqa i' j')) [ ( i' ∨ ~ i' ∨ j' ∨ ~ j' ) ↦ sqb-hollow i' j' ]
  --       sqb i' j' = inS (comp (λ k → B (spread i j i' j' k)) (
  --                       λ where
  --                           k (i' = i0) → LemmaL (~ k) j'
  --                           k (i' = i1) → LemmaR (~ k) j'
  --                           k (j' = i0) → LemmaU (~ k) i'
  --                           k (j' = i1) → LemmaD (~ k) i') (outS (sqb' i' j')))

  --   -- -- This is the proof in the style of the Cubical library: Cubical.Foundations.HLevels
  --   -- SqFillSigmaAB' : SqFill (Σ A (λ a → B a))
  --   -- SqFillSigmaAB' l r u d i j .fst = SqFillA (cong fst l) (cong fst r) (cong fst u) (cong fst d) i j
  --   -- SqFillSigmaAB' {lu} {ld} l {ru} {rd} r u d i j .snd =
  --   --     pathToPathP (λ i → PathP (λ j → SqB i j) (u i .snd) (d i .snd)) (cong snd l) (cong snd r)
  --   --     (SqFill→PathPIsProp (λ j → SqB i1 j) (SqFillB (sqA i1 i1)) (snd ru) (snd rd) (transport (λ i → PathP (λ j → SqB i j) (u i .snd) (d i .snd)) (cong snd l)) (cong snd r) )
  --   --     i j
  --   --     where
  --   --     sqA : I → I → A
  --   --     sqA i j = (SqFillA (cong fst l) (cong fst r) (cong fst u) (cong fst d) i j)

  --   --     SqB : I → I → Type
  --   --     SqB i j = B (sqA i j)

  --   --     -- the key idea is
  --   --     pathToPathP : (A : I → Type) (x : A i0) (y : A i1) → transport (λ i → A i) x ≡ y → PathP A x y
  --   --     pathToPathP A x y p i = hcomp (λ j → λ {
  --   --         (i = i0) → x;
  --   --         (i = i1) → p j
  --   --         }) (transp (λ j → A (i ∧ j)) (~ i) x)


  --   --     -- These modules are Glue-free.
  --   --     open import Cubical.Foundations.Prelude using (ℓ-max; symP; toPathP; hfill; fromPathP)
  --   --     open import Cubical.Foundations.GroupoidLaws using (hcomp-unique)

  --   --     -- The modules below are Gluey. To make it convincing, let's just copy the required definitions.
  --   --     -- open import Cubical.Foundations.Isomorphism using (Iso)
  --   --     -- open import Cubical.Foundations.Path using (PathPIsoPath)
  --   --     -- open import Cubical.Foundations.HLevels using (isPropRetract)
  --   --     module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} where
  --   --         section : (f : A → B) → (g : B → A) → Type ℓ'
  --   --         section f g = ∀ b → f (g b) ≡ b

  --   --         -- NB: `g` is the retraction!
  --   --         retract : (f : A → B) → (g : B → A) → Type ℓ
  --   --         retract f g = ∀ a → g (f a) ≡ a

  --   --     record Iso {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  --   --         no-eta-equality
  --   --         constructor iso
  --   --         field
  --   --             fun : A → B
  --   --             inv : B → A
  --   --             rightInv : section fun inv
  --   --             leftInv  : retract fun inv

  --   --     PathPIsoPath : ∀ {ℓ} (A : I → Type ℓ) (x : A i0) (y : A i1) → Iso (PathP A x y) (transport (λ i → A i) x ≡ y)
  --   --     PathPIsoPath A x y .Iso.fun = fromPathP
  --   --     PathPIsoPath A x y .Iso.inv = toPathP
  --   --     PathPIsoPath A x y .Iso.rightInv q k i =
  --   --         hcomp
  --   --         (λ j → λ
  --   --             { (i = i0) → slide (j ∨ ~ k)
  --   --             ; (i = i1) → q j
  --   --             ; (k = i0) → transp (λ l → A (i ∨ l)) i (fromPathPFiller j)
  --   --             ; (k = i1) → ∧∨Square i j
  --   --             })
  --   --         (transp (λ l → A (i ∨ ~ k ∨ l)) (i ∨ ~ k)
  --   --             (transp (λ l → (A (i ∨ (~ k ∧ l)))) (k ∨ i)
  --   --             (transp (λ l → A (i ∧ l)) (~ i)
  --   --                 x)))
  --   --         where
  --   --         fromPathPFiller : _
  --   --         fromPathPFiller =
  --   --             hfill
  --   --                 (λ j → λ
  --   --                 { (i = i0) → x
  --   --                 ; (i = i1) → q j })
  --   --                 (inS (transp (λ j → A (i ∧ j)) (~ i) x))

  --   --         slide : I → _
  --   --         slide i = transp (λ l → A (i ∨ l)) i (transp (λ l → A (i ∧ l)) (~ i) x)

  --   --         ∧∨Square : I → I → _
  --   --         ∧∨Square i j =
  --   --             hcomp
  --   --                 (λ l → λ
  --   --                 { (i = i0) → slide j
  --   --                 ; (i = i1) → q (j ∧ l)
  --   --                 ; (j = i0) → slide i
  --   --                 ; (j = i1) → q (i ∧ l)
  --   --                 })
  --   --                 (slide (i ∨ j))
  --   --     PathPIsoPath A x y .Iso.leftInv q k i =
  --   --         outS
  --   --         (hcomp-unique
  --   --             (λ j → λ
  --   --             { (i = i0) → x
  --   --             ; (i = i1) → transp (λ l → A (j ∨ l)) j (q j)
  --   --             })
  --   --             (inS (transp (λ l → A (i ∧ l)) (~ i) x))
  --   --             (λ j → inS (transp (λ l → A (i ∧ (j ∨ l))) (~ i ∨ j) (q (i ∧ j)))))
  --   --         k

  --   --     isPropRetract : ∀ {ℓ} → {A B : Type ℓ} (f : A → B) (g : B → A) (h : (x : A) → g (f x) ≡ x) → isProp B → isProp A
  --   --     isPropRetract f g h p x y i =
  --   --         hcomp
  --   --         (λ j → λ
  --   --             { (i = i0) → h x j
  --   --             ; (i = i1) → h y j})
  --   --         (g (p (f x) (f y) i))

  --   --     -- Kan operations hidden in:
  --   --     -- - isPropRetract has 1 hcomp
  --   --     -- - PathPIsoPath .Iso.leftInv needs uniqueness of hcomp, and also several hcomps
  --   --     SqFill→PathPIsProp : (A : I → Type) (SqFillA : SqFill (A i1)) (x : A i0) (y : A i1) → isProp (PathP A x y)
  --   --     SqFill→PathPIsProp A SqFillA x y = isPropRetract fromPathP (pathToPathP A x y) (PathPIsoPath A x y .Iso.leftInv) (λ p q → SqFillA p q refl refl)

  -- -- data _+_ (A B : Type) : Type where
  -- --     inl : A → A + B
  -- --     inr : B → A + B

  -- -- data ⊥ : Type where

  -- -- ⊥-elim : {A : Type} (x : ⊥) → A
  -- -- ⊥-elim ()

  -- -- data ⊤ : Type where
  -- --     tt : ⊤

  -- -- module SqFillCpdt (A A' : Type) (SqFillA : SqFill A) (SqFillA' : SqFill A') where
  -- --   inl≠inr : {A B : Type} (x : A) (y : B) → (inl x ≡ inr y) → ⊥
  -- --   inl≠inr {A} {B} x y p = transport (cong isLeft p) tt
  -- --       where
  -- --       isLeft : (A + B) → Type
  -- --       isLeft (inl x) = ⊤
  -- --       isLeft (inr y) = ⊥

  -- --   Cover : {A B : Type} (c c' : A + B) → Type
  -- --   Cover (inl x) (inl y) = x ≡ y
  -- --   Cover (inr x) (inr y) = x ≡ y
  -- --   Cover _ _ = ⊥

  -- --   reflCode : {A B : Type} (c : A + B) → Cover c c
  -- --   reflCode (inl x) = refl
  -- --   reflCode (inr x) = refl

  -- --   encode : {A B : Type} {c c' : A + B} → c ≡ c' → Cover c c'
  -- --   encode {c = c} p = transport (λ i → Cover c (p i)) (reflCode c)

  -- --   decode : {A B : Type} {c c' : A + B} → Cover c c' → c ≡ c'
  -- --   decode {c = inl x} {c' = inl y} = cong inl
  -- --   decode {c = inr x} {c' = inr y} = cong inr

  -- --   decodeEncode : {A B : Type} {c c' : A + B} (p : c ≡ c') → decode (encode p) ≡ p
  -- --   -- decodeEncode {c = inl x} = J (λ c' p → decode (encode p) ≡ p) (cong (cong inl) (transportRefl refl))
  -- --   decodeEncode {c = inl x} = J (λ c' p → decode (encode p) ≡ p) (cong (cong inl) (transportRefl refl))
  -- --   decodeEncode {c = inr x} = J (λ c' p → decode (encode p) ≡ p) (cong (cong inr) (transportRefl refl))

  -- --   SqFillCoproduct : SqFill (A + A')
  -- --   SqFillCoproduct {inl lu} {inl ld} l {inl ru} {inl rd} r u d i j =
  -- --       (hcomp (λ where
  -- --           k (i = i0) → decodeEncode l k j
  -- --           k (i = i1) → decodeEncode r k j
  -- --           k (j = i0) → decodeEncode u k i
  -- --           k (j = i1) → decodeEncode d k i)
  -- --       (inl {A} {A'} (SqFillA (encode l) (encode r) (encode u) (encode d) i j)))
  -- --   SqFillCoproduct {inr lu} {inr ld} l {inr ru} {inr rd} r u d i j =
  -- --       (hcomp (λ where
  -- --           k (i = i0) → decodeEncode l k j
  -- --           k (i = i1) → decodeEncode r k j
  -- --           k (j = i0) → decodeEncode u k i
  -- --           k (j = i1) → decodeEncode d k i)
  -- --       (inr {A} {A'} (SqFillA' (encode l) (encode r) (encode u) (encode d) i j)))
  -- --   SqFillCoproduct {inl x} {inr y} l _ _ _ = ⊥-elim (inl≠inr x y l)
  -- --   SqFillCoproduct {inr x} {inl y} l _ _ _ = ⊥-elim (inl≠inr y x (sym l))
  -- --   SqFillCoproduct {inl x} {_} _ {inr y} _ u _ = ⊥-elim (inl≠inr x y u)
  -- --   SqFillCoproduct {inr x} {_} _ {inl y} _ u _ = ⊥-elim (inl≠inr y x (sym u))
  -- --   SqFillCoproduct {_} {inl x} _ {_} {inr y} _ _ d = ⊥-elim (inl≠inr x y d)
  -- --   SqFillCoproduct {_} {inr x} _ {_} {inl y} _ _ d = ⊥-elim (inl≠inr y x (sym d))
  -- --   -- SqFillCoproduct {_} {_} _ {inl x} {inr y} r _ _ = ⊥-elim (inl≠inr x y r)
  -- --   -- SqFillCoproduct {_} {_} _ {inr x} {inl y} r _ _ = ⊥-elim (inl≠inr y x (sym r))

  -- -- module SqFillPath (A : Type) (SqFillA : SqFill A) where
  -- --   SqFillPath : {a b : A} → SqFill (a ≡ b)
  -- --   SqFillPath {_} {_} {lu} l r u d i j =
  -- --       hcomp (λ k → λ {(i = i0) → isPropa≡b lu (l j) k
  -- --                   ; (i = i1) → isPropa≡b lu (r j) k
  -- --                   ; (j = i0) → isPropa≡b lu (u i) k
  -- --                   ; (j = i1) → isPropa≡b lu (d i) k}) lu
  -- --       where
  -- --       isPropa≡b : {a b : A} (p q : a ≡ b) → p ≡ q
  -- --       isPropa≡b p q = SqFillA p q refl refl

  -- -- data W (S : Type) (P : S → Type) : Type where
  -- --   sup-W : (s : S) → (P s → W S P) → W S P

  -- -- data Bool : Type where
  -- --   true : Bool
  -- --   false : Bool

  -- -- NatW : Type
  -- -- NatW = W Bool λ { true → ⊥ ; false → ⊤}

  -- -- data ℕ : Type where
  -- --   zero : ℕ
  -- --   suc : ℕ → ℕ

  -- -- Nat→NatW : ℕ → NatW
  -- -- Nat→NatW zero = sup-W true (λ ())
  -- -- Nat→NatW (suc n) = sup-W false (λ tt → Nat→NatW n)

  -- -- NatW→Nat : NatW → ℕ
  -- -- NatW→Nat (sup-W true x) = zero
  -- -- NatW→Nat (sup-W false x) = suc (NatW→Nat (x tt))

  -- -- invℕ : (n : ℕ) → NatW→Nat (Nat→NatW n) ≡ n
  -- -- invℕ zero = refl
  -- -- invℕ (suc n) = cong suc (invℕ n)

  -- -- invNatW : (x : NatW) → Nat→NatW (NatW→Nat x) ≡ x
  -- -- invNatW (sup-W true x) = cong (sup-W true) {!!}
  -- -- invNatW (sup-W false x) = cong (sup-W false) {!λ i tt → invNatW (x tt)!}

  -- -- doubleW : NatW → NatW
  -- -- doubleW (sup-W true x) = sup-W true x
  -- -- doubleW (sup-W false x) = sup-W false (λ _ → sup-W false (λ _ → sup-W true λ ()))

  -- -- W-elim : ∀ {S P} → (B : W S P → Type) → (Bsup-W : (s : S) → (f : P s → W S P) → B (sup-W s f)) → (w : W S P) → B w
  -- -- W-elim {S} {P} B Bsup-W (sup-W s x) = Bsup-W s x

  -- -- module SqFillW
  -- --   (S : Type) (P : S → Type)
  -- --   (SqFillS : SqFill S) (SqFillP : (s : S) → SqFill (P s))
  -- --   where

  -- --   CoverW : (x y : W S P) → Type
  -- --   CoverW (sup-W s x) (sup-W s' x') = Σ[ p ∈ s ≡ s' ] PathP (λ i → (P (p i) → W S P)) x x'

  -- --   reflCodeW : {x : W S P} → CoverW x x
  -- --   reflCodeW {sup-W s x} = refl , refl

  -- --   encodeW : {x y : W S P} → x ≡ y → CoverW x y
  -- --   encodeW {x} p = transport (λ i → CoverW x (p i)) reflCodeW

  -- --   encodeReflW : {x : W S P} → encodeW (refl {x = x}) ≡ reflCodeW {x = x}
  -- --   encodeReflW {x = sup-W s x} i .fst = transp (λ _ → s ≡ s) i refl
  -- --   encodeReflW {x = sup-W s x} i .snd = λ j z → {!!}
  -- --     -- transp (λ j → PathP (λ k → P (encodeReflW {x = sup-W s x} i .fst k) → W S P) x x) i
  -- --     --        (λ j → {!transp (λ k → P (encodeReflW {x = sup-W s x} i .fst j) → W S P) (((~ j) ∨ j) ∨ i) x!})

  -- --   decodeW : {x y : W S P} → CoverW x y → x ≡ y
  -- --   decodeW {x = sup-W s x} {y = sup-W s' x'} (ps , px) = cong₂ sup-W ps px

  -- --   encodeDecodeW : (x y : W S P) → (c : CoverW x y) → encodeW (decodeW c) ≡ c
  -- --   encodeDecodeW (sup-W s x) (sup-W s' x') (ps , px) i .fst = {!transp (λ _ → s ≡ (ps i)) i !}
  -- --   encodeDecodeW (sup-W s x) (sup-W s' x') (ps , px) i .snd = {!!}

  -- --   -- open import Cubical.Foundations.Prelude using (cong₂)
  -- --   decodeEncodeW : {x y : W S P} → (p : x ≡ y) → decodeW (encodeW p) ≡ p
  -- --   decodeEncodeW {sup-W s x} {y} =
  -- --     J (λ y p → decodeW (encodeW p) ≡ p)
  -- --       -- (λ i → cong₂ sup-W (transportRefl (refl {x = s}) i) λ j → transportRefl {!!} i)
  -- --       (λ i → cong₂ sup-W (transp (λ _ → s ≡ s) i (refl {x = s})) (transp (λ _ → PathP {!λ i → P (transportRefl s i) → W S P!} x x) i (refl {x = x})))
  -- --       -- {!cong (cong₂ sup-W) (transportRefl ?)!}
  -- --       {y}

  -- --   SqFillW : SqFill (W S P)
  -- --   SqFillW {sup-W slu xlu} {sup-W sld xld} l {sup-W sru xru} {sup-W srd xrd} r u d i j =
  -- --       (hcomp (λ where
  -- --           k (i = i0) → decodeEncodeW l k j
  -- --           k (i = i1) → decodeEncodeW r k j
  -- --           k (j = i0) → decodeEncodeW u k i
  -- --           k (j = i1) → decodeEncodeW d k i)
  -- --       (sup-W (sqs i j) {!SqFillP (sqs i j) (encodeW)  !}))
  -- --       where
  -- --         open SqFillSigma
  -- --         open SqFillPi
  -- --         SqFillPs→WSP : (s : S) → SqFill (P s → W S P)
  -- --         SqFillPs→WSP s = {!SqFillPiAB (P s) (λ _ → W S P) ()!}

  -- --         -- SqFillCoverW : (w : W S P) → SqFill (CoverW w w)
  -- --         -- SqFillCover (sup-W s x) = {! SqFillSigmaAB S SqFillS (λ s → (P s → W S P)) (λ s → SqFillPs→WSP s) !}

  -- --         sqs = SqFillS (encodeW l .fst) (encodeW r .fst) (encodeW u .fst) (encodeW d .fst)
  -- --     -- {!sup-W (SqFillS ? ? ? ? i j) ?!}

  -- -- -- PathP types
  -- -- -- Regular Inductive types (Indexed-W Types)
  -- -- -- HITs (just add hidden uip contrctor)
  -- -- -- Universe
  -- -- -- lemma: UIP after transport
  -- -- -- ifwe have hcomped paths, transporting along it is just transporting along the open box
  -- -- -- andreas's example: a hollow square in the universe, the bottom square is the constant top left type,
  -- -- -- can the types of the faces be the same
  -- -- --
  -- -- -- Injectivity of type formers: bool to bool is not equal to top to 4
  -- -- -- Injectivity of type formers in OTT?
  -- -- -- McBride's "John Major" equality (of heterogeneous equality. can it help with the Pi/Sigma complication?)
  -- -- --

  -- --   -- data int : Type where
  -- --   --   zero : int
  -- --   --   succ : int → int
  -- --   --   pred : int → int
  -- --   --   sp : succ pred n ≡
