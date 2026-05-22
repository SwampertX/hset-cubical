-- If you are running mainline Agda, use --cubical
{-# OPTIONS --cubical #-}

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
-- open import Agda.Builtin.Coproduct renaming (_⊎_ to _+_)
-- open import Agda.Builtin.Product

module SqFill where
  SqFill : (A : Type) → Type
  SqFill A =
    (a₀₀ : A) (a₀₁ : A) (a₀₋ : a₀₀ ≡ a₀₁)
    (a₁₀ : A) (a₁₁ : A) (a₁₋ : a₁₀ ≡ a₁₁)
    (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
    → PathP (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋

  -- {-# BUILTIN SQFILL SqFill #-}

  open import Helper

  module SqFillPi (A : Type) (B : A → Type) (SqFillB : (x : A) → SqFill (B x)) where

    SqFillPiAB : SqFill ((a : A) → B a)
    SqFillPiAB lu ld l ru rd r u d i j a = SqFillB a (lu a) (ld a) (λ i → l i a) (ru a) (rd a) (λ i → r i a) (λ i → u i a) (λ i → d i a) i j

  -- {-# BUILTIN SQFILLPI SqFillPi.SqFillPiAB #-}

  if_then_else_end : I → I → I → I
  if i then j else k end = (k ∧ (~ i ∨ j)) ∨ ((i ∨ k) ∧ j)

  {-# INLINE if_then_else_end #-}

  -- module SqFillSigma (A : Type) (SqFillA : SqFill A) (B : A → Type) (SqFillB : (x : A) → SqFill (B x)) where

  --   SqFillSigmaAB : SqFill (Σ A (λ a → B a))
  --   SqFillSigmaAB {lu} {ld} l {ru} {rd} r u d i j .fst = SqFillA (cong fst l) (cong fst r) (cong fst u) (cong fst d) i j
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

  -- {-# BUILTIN SQFILLSIGMA SqFillSigma.SqFillSigmaAB #-}

  -- module SqFillProduct (A : Type) (SqFillA : SqFill A) (B : Type) (SqFillB : SqFill B) where

  --   SqFillProductAB : SqFill (A × B)
  --   SqFillProductAB {lu} {ld} l {ru} {rd} r u d i j .fst = SqFillA (cong fst l) (cong fst r) (cong fst u) (cong fst d) i j
  --   SqFillProductAB {lu} {ld} l {ru} {rd} r u d i j .snd = SqFillB (cong snd l) (cong snd r) (cong snd u) (cong snd d) i j

  -- {-# BUILTIN SQFILLPRODUCT SqFillProduct.SqFillProductAB #-}

  -- data ⊥ : Type where

  -- ⊥-elim : {A : Type} (x : ⊥) → A
  -- ⊥-elim ()

  -- open import Agda.Builtin.Unit

  -- module SqFillCoproduct (A : Type) (SqFillA : SqFill A) (A' : Type) (SqFillA' : SqFill A') where

  --   module EncodeDecode {A B : Type} where
  --       inl≠inr : (x : A) (y : B) → (inl x ≡ inr y) → ⊥
  --       inl≠inr x y p = transport (cong isLeft p) tt
  --           where
  --           isLeft : (A + B) → Type
  --           isLeft (inl x) = ⊤
  --           isLeft (inr y) = ⊥

  --       Cover : (c c' : A + B) → Type
  --       Cover (inl x) (inl y) = x ≡ y
  --       Cover (inr x) (inr y) = x ≡ y
  --       Cover _ _ = ⊥

  --       reflCode : (c : A + B) → Cover c c
  --       reflCode (inl x) = refl
  --       reflCode (inr x) = refl

  --       encode : {c c' : A + B} → c ≡ c' → Cover c c'
  --       encode {c = c} p = transport (λ i → Cover c (p i)) (reflCode c)

  --       decode : {c c' : A + B} → Cover c c' → c ≡ c'
  --       decode {c = inl x} {c' = inl y} = cong inl
  --       decode {c = inr x} {c' = inr y} = cong inr

  --       decodeEncode : {c c' : A + B} (p : c ≡ c') → decode (encode p) ≡ p
  --       decodeEncode {c = inl x} = J (λ c' p → decode (encode p) ≡ p) (cong (cong inl) (transportRefl refl))
  --       decodeEncode {c = inr x} = J (λ c' p → decode (encode p) ≡ p) (cong (cong inr) (transportRefl refl))

  --   open EncodeDecode

  --   SqFillCoproduct : SqFill (A + A')
  --   SqFillCoproduct {inl lu} {inl ld} l {inl ru} {inl rd} r u d i j =
  --       (hcomp (λ where
  --           k (i = i0) → decodeEncode l k j
  --           k (i = i1) → decodeEncode r k j
  --           k (j = i0) → decodeEncode u k i
  --           k (j = i1) → decodeEncode d k i)
  --       (inl {A = A} {B = A'} (SqFillA (encode l) (encode r) (encode u) (encode d) i j)))
  --   SqFillCoproduct {inr lu} {inr ld} l {inr ru} {inr rd} r u d i j =
  --       (hcomp (λ where
  --           k (i = i0) → decodeEncode l k j
  --           k (i = i1) → decodeEncode r k j
  --           k (j = i0) → decodeEncode u k i
  --           k (j = i1) → decodeEncode d k i)
  --       (inr {A = A} {B = A'} (SqFillA' (encode l) (encode r) (encode u) (encode d) i j)))
  --   SqFillCoproduct {inl x} {inr y} l _ _ _ = ⊥-elim (inl≠inr x y l)
  --   SqFillCoproduct {inr x} {inl y} l _ _ _ = ⊥-elim (inl≠inr y x (sym l))
  --   SqFillCoproduct {inl x} {_} _ {inr y} _ u _ = ⊥-elim (inl≠inr x y u)
  --   SqFillCoproduct {inr x} {_} _ {inl y} _ u _ = ⊥-elim (inl≠inr y x (sym u))
  --   SqFillCoproduct {_} {inl x} _ {_} {inr y} _ _ d = ⊥-elim (inl≠inr x y d)
  --   SqFillCoproduct {_} {inr x} _ {_} {inl y} _ _ d = ⊥-elim (inl≠inr y x (sym d))

  -- {-# BUILTIN SQFILLCOPRODUCT SqFillCoproduct.SqFillCoproduct #-}

  -- module SqFillPath (A : Type) (a b : A) (SqFillA : SqFill A)  where
  --   SqFillPath : SqFill (a ≡ b)
  --   SqFillPath {lu} l r u d i j =
  --       hcomp (λ k → λ {(i = i0) → isPropa≡b lu (l j) k
  --                     ; (i = i1) → isPropa≡b lu (r j) k
  --                     ; (j = i0) → isPropa≡b lu (u i) k
  --                     ; (j = i1) → isPropa≡b lu (d i) k}) lu
  --       where
  --       isPropa≡b : (p q : a ≡ b) → p ≡ q
  --       isPropa≡b p q = SqFillA p q refl refl

  -- {-# BUILTIN SQFILLPATH SqFillPath.SqFillPath #-}

  -- -- Only one of SqFillA or SqFillB is needed. Currently we request for both an only use SqFillA.
  -- module SqFillPathP (A B : Type) (a : A) (b : B) (P : A ≡ B) (SqFillA : SqFill A) where
  --   SqFillPathP : SqFill (PathP (λ i → P i) a b)
  --   SqFillPathP {lu} l r u d i j =
  --       hcomp (λ k → λ {(i = i0) → isPropa≡b lu (l j) k
  --                     ; (i = i1) → isPropa≡b lu (r j) k
  --                     ; (j = i0) → isPropa≡b lu (u i) k
  --                     ; (j = i1) → isPropa≡b lu (d i) k}) lu
  --       where
  --       isPropa≡b : (p q : PathP (λ k → P k) a b) → p ≡ q
  --       isPropa≡b p q i k =
  --         comp (λ l → P (k ∧ l))
  --              (λ l → λ{(k = i0) → a ;
  --                       (k = i1) → transp (λ j → P (l ∨ (~ j))) l b ;
  --                       (i = i0) → wallp (~ l) k ;
  --                       (i = i1) → wallq (~ l) k })
  --              (SqFillA pa qa (refl {x = a}) (refl {x = transport (sym P) b}) i k)
  --         where
  --           pa : a ≡ transport (sym P) b
  --           pa k = transp (λ l → P ((~ l) ∧ k)) (~ k) (p k)
  --           qa : a ≡ transport (sym P) b
  --           qa k = transp (λ l → P ((~ l) ∧ k)) (~ k) (q k)

  --           wallp : PathP (λ l → PathP (λ k → P (k ∧ ~ l)) a (transp (λ k → P (~ l ∨ ~ k)) (~ l) b)) p pa
  --           wallp l k = transp (λ j → P (k ∧ ~ (l ∧ j))) (~ (k ∧ l)) (p k)
  --           wallq : PathP (λ l → PathP (λ k → P (k ∧ ~ l)) a (transp (λ k → P (~ l ∨ ~ k)) (~ l) b)) q qa
  --           wallq l k = transp (λ j → P (k ∧ ~ (l ∧ j))) (~ (k ∧ l)) (q k)

  -- {-# BUILTIN SQFILLPATHP SqFillPathP.SqFillPathP #-}

  -- -- TODO: can we request for (SqFill A ⊎ SqFill B) and have a term that adjusts?
  -- --   this then requires the filling to be done symmetrically wrt A and B (not too hard)
  -- -- module SqFillPathP' (A B : Type) (P : A ≡ B) (SqFillAorB : SqFill A ⊎ SqFill B) where
  -- --   SqFillPathP : {a : A} {b : B} → SqFill (PathP (λ i → P i) a b)
  -- --   SqFillPathP {a} {b} {lu} {ld} l r u d i j =
  -- --       hcomp (λ k → λ {(i = i0) → isPropa≡b lu (l j) k
  -- --                     ; (i = i1) → isPropa≡b lu (r j) k
  -- --                     ; (j = i0) → isPropa≡b lu (u i) k
  -- --                     ; (j = i1) → isPropa≡b lu (d i) k}) lu
  -- --       where
  -- --       isPropa≡b : {a : A} {b : B} (p q : PathP (λ k → P k) a b) → p ≡ q
  -- --       isPropa≡b {a} {b} p q i k =
  -- --         comp (λ l → P (k ∧ l))
  -- --              (λ l → λ{(k = i0) → a ;
  -- --                       (k = i1) → transp (λ j → P (l ∨ (~ j))) l b ;
  -- --                       (i = i0) → wallp (~ l) k ;
  -- --                       (i = i1) → wallq (~ l) k })
  -- --              (SqFillA pa qa (refl {x = a}) (refl {x = transport (sym P) b}) i k)
  -- --         where
  -- --           pa : a ≡ transport (sym P) b
  -- --           pa k = transp (λ l → P ((~ l) ∧ k)) (~ k) (p k)
  -- --           qa : a ≡ transport (sym P) b
  -- --           qa k = transp (λ l → P ((~ l) ∧ k)) (~ k) (q k)

  -- --           wallp : PathP (λ l → PathP (λ k → P (k ∧ ~ l)) a (transp (λ k → P (~ l ∨ ~ k)) (~ l) b)) p pa
  -- --           wallp l k = transp (λ j → P (k ∧ ~ (l ∧ j))) (~ (k ∧ l)) (p k)
  -- --           wallq : PathP (λ l → PathP (λ k → P (k ∧ ~ l)) a (transp (λ k → P (~ l ∨ ~ k)) (~ l) b)) q qa
  -- --           wallq l k = transp (λ j → P (k ∧ ~ (l ∧ j))) (~ (k ∧ l)) (q k)

  -- module SqFillUnit where
  --   SqFillUnit : SqFill ⊤
  --   SqFillUnit {tt} {tt} l {tt} {tt} r u d i j =
  --       hcomp (λ k → λ {(i = i0) → isProp⊤ tt (l j) k
  --                     ; (i = i1) → isProp⊤ tt (r j) k
  --                     ; (j = i0) → isProp⊤ tt (u i) k
  --                     ; (j = i1) → isProp⊤ tt (d i) k}) tt
  --       where
  --       isProp⊤ : (a b : ⊤) → a ≡ b
  --       isProp⊤ tt tt _ = tt

  -- {-# BUILTIN SQFILLUNIT SqFillUnit.SqFillUnit #-}

  -- module SqFillBool where
  --   open import Agda.Builtin.Bool

  --   true≠false : true ≡ false → ⊥
  --   true≠false p = transport (cong isTrue p) tt
  --       where
  --       isTrue : Bool → Type
  --       isTrue true = ⊤
  --       isTrue false = ⊥

  --   K-Bool : (P : {b : Bool} → b ≡ b → Type)
  --       → (∀{b} → P {b} refl)
  --       → ∀{b} → (q : b ≡ b) → P q
  --   K-Bool P Pr {false} = J (λ{ false q → P q ; true _ → ⊥ }) Pr
  --   K-Bool P Pr {true}  = J (λ{ true q → P q ; false _ → ⊥ }) Pr

  --   KBool : {b : Bool} → (p : b ≡ b) → p ≡ refl
  --   KBool {true} = J (λ{ true q → q ≡ refl ; false _ → ⊥ }) refl
  --   KBool {false} = J (λ{ false q → q ≡ refl ; true _ → ⊥ }) refl

  --   -- it's also possible to implement this term by inspecting the paths instead
  --   -- then sqfill refl refl refl refl would definitionally to our term
  --   -- but right now it doesn't (Jrefl is not definitional)
  --   SqFillBool : SqFill Bool
  --   SqFillBool {true} {true} l {true} {true} r u d i j =
  --     (hcomp (λ where k (i = i0) → KBool l (~ k) j
  --                     k (i = i1) → KBool r (~ k) j
  --                     k (j = i0) → KBool u (~ k) i
  --                     k (j = i1) → KBool d (~ k) i) true)
  --   SqFillBool {false} {false} l {false} {false} r u d i j =
  --     (hcomp (λ where k (i = i0) → KBool l (~ k) j
  --                     k (i = i1) → KBool r (~ k) j
  --                     k (j = i0) → KBool u (~ k) i
  --                     k (j = i1) → KBool d (~ k) i) false)
  --   SqFillBool {true} {false} l _ _ _ = ⊥-elim (true≠false l)
  --   SqFillBool {false} {true} l _ _ _ = ⊥-elim (true≠false (sym l))
  --   SqFillBool {true} {_} _ {false} _ u _ = ⊥-elim (true≠false u)
  --   SqFillBool {false} {_} _ {true} _ u _ = ⊥-elim (true≠false (sym u))
  --   SqFillBool {_} {true} _ {_} {false} _ _ d = ⊥-elim (true≠false d)
  --   SqFillBool {_} {false} _ {_} {true} _ _ d = ⊥-elim (true≠false (sym d))

  -- {-# BUILTIN SQFILLBOOL SqFillBool.SqFillBool #-}

  -- open import Agda.Builtin.Nat

  -- module SqFillNat where
  --   zero≠suc : {n : Nat} → zero ≡ suc n → ⊥
  --   zero≠suc p = transport (cong isZero p) tt
  --       where
  --       isZero : Nat → Type
  --       isZero zero = ⊤
  --       isZero (suc _) = ⊥

  --   NatCover : (n n' : Nat) → Type
  --   NatCover zero zero = ⊤
  --   NatCover (suc n) (suc n') = NatCover n n'
  --   NatCover _ _ = ⊥

  --   reflCode : (n : Nat) → NatCover n n
  --   reflCode zero = tt
  --   reflCode (suc n) = reflCode n

  --   encode : (n n' : Nat) → n ≡ n' → NatCover n n'
  --   encode n n' = J (λ n' _ → NatCover n n') (reflCode n)

  --   decode : (n n' : Nat) → NatCover n n' → n ≡ n'
  --   decode zero zero tt = refl
  --   decode (suc n) (suc n') c = cong suc (decode n n' c)

  --   encodeDecode : (n n' : Nat) (c : NatCover n n') → encode n n' (decode n n' c) ≡ c
  --   encodeDecode zero zero c = refl
  --   encodeDecode (suc n) (suc n') c = encodeDecode n n' c

  --   decodeEncode : (n n' : Nat) (p : n ≡ n') → decode n n' (encode n n' p) ≡ p
  --   decodeEncode zero n' = J (λ n' p → decode zero n' (encode zero n' p) ≡ p) refl
  --   decodeEncode (suc n) n' = J (λ n' p → decode (suc n) n' (encode (suc n) n' p) ≡ p) (cong (cong suc) (decodeEncode n n refl))


  --   SqFillNat : SqFill Nat
  --   SqFillNat {zero} {zero} l {zero} {zero} r u d i j =
  --     (hcomp (λ where k (i = i0) → decodeEncode _ _ l k j
  --                     k (i = i1) → decodeEncode _ _ r k j
  --                     k (j = i0) → decodeEncode _ _ u k i
  --                     k (j = i1) → decodeEncode _ _ d k i) zero)
  --   SqFillNat {suc lu} {suc ld} l {suc ru} {suc rd} r u d i j =
  --     (hcomp (λ where k (i = i0) → decodeEncode (suc lu) (suc ld) l k j
  --                     k (i = i1) → decodeEncode (suc ru) (suc rd) r k j
  --                     k (j = i0) → decodeEncode (suc lu) (suc ru) u k i
  --                     k (j = i1) → decodeEncode (suc ld) (suc rd) d k i) (
  --           suc (SqFillNat {lu} (decode lu ld (encode _ _ l))
  --                               (decode ru rd (encode _ _ r))
  --                               (decode lu ru (encode _ _ u))
  --                               (decode ld rd (encode _ _ d)) i j)))
  --   -- more explicit version with pred
  --   -- SqFillNat {suc lu} {suc ld} l {suc ru} {suc rd} r u d i j =
  --   --   (hcomp (λ where k (i = i0) → decodeEncode (suc lu) (suc ld) l k j
  --   --                   k (i = i1) → decodeEncode (suc ru) (suc rd) r k j
  --   --                   k (j = i0) → decodeEncode (suc lu) (suc ru) u k i
  --   --                   k (j = i1) → decodeEncode (suc ld) (suc rd) d k i) (
  --   --         suc (SqFillNat {lu} (cong pred (decode (suc lu) (suc ld) (encode _ _ l)))
  --   --                   (cong pred (decode (suc ru) (suc rd) (encode _ _ r)))
  --   --                   (cong pred (decode (suc lu) (suc ru) (encode _ _ u)))
  --   --                   (cong pred (decode (suc ld) (suc rd) (encode _ _ d))) i j)))
  --   --   where
  --   --     pred : Nat → Nat
  --   --     pred zero = zero
  --   --     pred (suc n) = n
  --   SqFillNat {zero} {suc _} l {_} {_} _ _ _ = ⊥-elim (zero≠suc l)
  --   SqFillNat {suc _} {zero} l {_} {_} _ _ _ = ⊥-elim (zero≠suc (sym l))
  --   SqFillNat {zero} {_} _ {suc _} {_} _ u _ = ⊥-elim (zero≠suc u)
  --   SqFillNat {suc _} {_} _ {zero} {_} _ u _ = ⊥-elim (zero≠suc (sym u))
  --   SqFillNat {_} {zero} _ {_} {suc _} _ _ d = ⊥-elim (zero≠suc d)
  --   SqFillNat {_} {suc _} _ {_} {zero} _ _ d = ⊥-elim (zero≠suc (sym d))

  -- {-# BUILTIN SQFILLNAT SqFillNat.SqFillNat #-}

  -- open import Agda.Builtin.List
  -- module SqFillList (A : Type) (sqFillA : SqFill A) where

  --   nil≠cons : {x : A} {xs : List A} → [] ≡ x ∷ xs → ⊥
  --   nil≠cons p = transport (cong isNil p) tt
  --       where
  --       isNil : List A → Type
  --       isNil [] = ⊤
  --       isNil (_ ∷ _) = ⊥

  --   ListCover : (xs ys : List A) → Type
  --   ListCover [] [] = ⊤
  --   ListCover (x ∷ xs) (y ∷ ys) = (x ≡ y) × (ListCover xs ys)
  --   ListCover _ _ = ⊥

  --   reflCode : (xs : List A) → ListCover xs xs
  --   reflCode [] = tt
  --   reflCode (x ∷ xs) = refl , reflCode xs

  --   encode : (xs ys : List A) → xs ≡ ys → ListCover xs ys
  --   encode xs ys = J (λ ys _ → ListCover xs ys) (reflCode xs)

  --   encodeRefl : (xs : List A) → encode xs xs refl ≡ reflCode xs
  --   encodeRefl xs = JRefl (λ ys _ → ListCover xs ys) (reflCode xs)

  --   decode : (xs ys : List A) → ListCover xs ys → xs ≡ ys
  --   decode [] [] tt = refl
  --   decode (x ∷ xs) (y ∷ ys) (p , c) = cong₂ _∷_ p (decode xs ys c)

  --   decodeRefl : (xs : List A) → decode xs xs (reflCode xs) ≡ refl
  --   decodeRefl [] = refl
  --   decodeRefl (x ∷ xs) = cong (cong₂ _∷_ refl) (decodeRefl xs)

  --   decodeEncode : (xs ys : List A) (p : xs ≡ ys) → decode xs ys (encode xs ys p) ≡ p
  --   decodeEncode xs _ = J (λ ys p → decode xs ys (encode xs ys p) ≡ p) (transport (λ i → decode xs xs (encodeRefl xs (~ i)) ≡ refl) (decodeRefl xs))

  --   SqFillList : SqFill (List A)
  --   SqFillList {[]} {[]} l {[]} {[]} r u d i j =
  --     (hcomp (λ where k (i = i0) → decodeEncode _ _ l k j
  --                     k (i = i1) → decodeEncode _ _ r k j
  --                     k (j = i0) → decodeEncode _ _ u k i
  --                     k (j = i1) → decodeEncode _ _ d k i) [])
  --   SqFillList {lu ∷ lus} {ld ∷ lds} l {ru ∷ rus} {rd ∷ rds} r u d i j =
  --     (hcomp (λ where k (i = i0) → decodeEncode (lu ∷ lus) (ld ∷ lds) l k j
  --                     k (i = i1) → decodeEncode (ru ∷ rus) (rd ∷ rds) r k j
  --                     k (j = i0) → decodeEncode (lu ∷ lus) (ru ∷ rus) u k i
  --                     k (j = i1) → decodeEncode (ld ∷ lds) (rd ∷ rds) d k i)
  --       (sqFillA (encode _ _ l .fst) (encode _ _ r .fst) (encode _ _ u .fst) (encode _ _ d .fst) i j
  --         ∷ SqFillList {lus} (decode _ _ (encode _ _ l .snd))
  --                              (decode _ _ (encode _ _ r .snd))
  --                              (decode _ _ (encode _ _ u .snd))
  --                              (decode _ _ (encode _ _ d .snd)) i j))
  --   SqFillList {[]} {_ ∷ _} l {_} {_} _ _ _ = ⊥-elim (nil≠cons l)
  --   SqFillList {_ ∷ _} {[]} l {_} {_} _ _ _ = ⊥-elim (nil≠cons (sym l))
  --   SqFillList {[]} {_} _ {_ ∷ _} {_} _ u _ = ⊥-elim (nil≠cons u)
  --   SqFillList {_ ∷ _} {_} _ {[]} {_} _ u _ = ⊥-elim (nil≠cons (sym u))
  --   SqFillList {_} {[]} _ {_} {_ ∷ _} _ _ d = ⊥-elim (nil≠cons d)
  --   SqFillList {_} {_ ∷ _} _ {_} {[]} _ _ d = ⊥-elim (nil≠cons (sym d))

  -- {-# BUILTIN SQFILLLIST SqFillList.SqFillList #-}

  -- -- -- An experiment with the cover as a list as well. Matches on indexed datatypes, unsupported
  -- -- module SqFillList' (A : Type) (sqFillA : SqFill A) where
  -- --   nil≠cons : {x : A} {xs : List A} → [] ≡ x ∷ xs → ⊥
  -- --   nil≠cons p = transport (cong isNil p) tt
  -- --       where
  -- --       isNil : List A → Type
  -- --       isNil [] = ⊤
  -- --       isNil (_ ∷ _) = ⊥

  -- --   data ListCover : List A → List A → Type where
  -- --     nilListCover : ListCover [] []
  -- --     consListCover : {x y : A} {xs ys : List A} → x ≡ y → ListCover xs ys → ListCover (x ∷ xs) (y ∷ ys)

  -- --   reflCode : (xs : List A) → ListCover xs xs
  -- --   reflCode [] = nilListCover
  -- --   reflCode (x ∷ xs) = consListCover refl (reflCode xs)

  -- --   encode : (xs ys : List A) → xs ≡ ys → ListCover xs ys
  -- --   encode xs ys = J (λ ys _ → ListCover xs ys) (reflCode xs)

  -- --   -- Warning: unsupported index matching
  -- --   -- decode : (xs ys : List A) → ListCover xs ys → xs ≡ ys
  -- --   -- decode [] [] nilListCover = refl
  -- --   -- decode (x ∷ xs) (y ∷ ys) (consListCover p ps) = cong₂ _∷_ p (decode xs ys ps)


  -- module SqFillMaybe (A : Type) (sqFillA : SqFill A) where
  --   open import Agda.Builtin.Maybe

  --   module EncodeDecode where
  --       nothing≠just : {x : A} → (nothing ≡ just x) → ⊥
  --       nothing≠just p = transport (cong isNothing p) tt
  --           where
  --           isNothing : Maybe A → Type
  --           isNothing nothing = ⊤
  --           isNothing (just y) = ⊥

  --       MaybeCover : (c c' : Maybe A) → Type
  --       MaybeCover nothing nothing = ⊤
  --       MaybeCover (just x) (just y) = x ≡ y
  --       MaybeCover _ _ = ⊥

  --       reflCode : (c : Maybe A) → MaybeCover c c
  --       reflCode nothing = tt
  --       reflCode (just x) = refl

  --       encode : {c c' : Maybe A} → c ≡ c' → MaybeCover c c'
  --       encode {c = c} p = transport (λ i → MaybeCover c (p i)) (reflCode c)

  --       decode : {c c' : Maybe A} → MaybeCover c c' → c ≡ c'
  --       decode {c = nothing} {c' = nothing} _ = refl
  --       decode {c = just x} {c' = just y} = cong just

  --       decodeEncode : {c c' : Maybe A} (p : c ≡ c') → decode (encode p) ≡ p
  --       decodeEncode {c = nothing} = J (λ c' p → decode (encode p) ≡ p) refl
  --       decodeEncode {c = just x} = J (λ c' p → decode (encode p) ≡ p) (cong (cong just) (transportRefl refl))

  --   open EncodeDecode

  --   SqFillMaybe : SqFill (Maybe A)
  --   SqFillMaybe {nothing} {nothing} l {nothing} {nothing} r u d i j =
  --       (hcomp (λ where
  --           k (i = i0) → decodeEncode l k j
  --           k (i = i1) → decodeEncode r k j
  --           k (j = i0) → decodeEncode u k i
  --           k (j = i1) → decodeEncode d k i) nothing)
  --   SqFillMaybe {just lu} {just ld} l {just ru} {just rd} r u d i j =
  --       (hcomp (λ where
  --           k (i = i0) → decodeEncode l k j
  --           k (i = i1) → decodeEncode r k j
  --           k (j = i0) → decodeEncode u k i
  --           k (j = i1) → decodeEncode d k i)
  --       (just (sqFillA (encode l) (encode r) (encode u) (encode d) i j)))
  --   SqFillMaybe {nothing} {just y} l _ _ _ = ⊥-elim (nothing≠just l)
  --   SqFillMaybe {just x} {nothing} l _ _ _ = ⊥-elim (nothing≠just (sym l))
  --   SqFillMaybe {nothing} {_} _ {just y} _ u _ = ⊥-elim (nothing≠just u)
  --   SqFillMaybe {just x} {_} _ {nothing} _ u _ = ⊥-elim (nothing≠just (sym u))
  --   SqFillMaybe {_} {nothing} _ {_} {just y} _ _ d = ⊥-elim (nothing≠just d)
  --   SqFillMaybe {_} {just x} _ {_} {nothing} _ _ d = ⊥-elim (nothing≠just (sym d))

  -- {-# BUILTIN SQFILLMAYBE SqFillMaybe.SqFillMaybe #-}

  -- -- module SqFillW
  -- --   (S : Type) (P : S → Type)
  -- --   (SqFillS : SqFill S) (SqFillP : (s : S) → SqFill (P s))
  -- --   where
  -- --
  -- --   data W (S : Type) (P : S → Type) : Type where
  -- --       sup-W : (s : S) → (P s → W S P) → W S P

  -- --   NatW : Type
  -- --   NatW = W Bool λ { true → ⊥ ; false → ⊤}


  -- --   Nat→NatW : ℕ → NatW
  -- --   Nat→NatW zero = sup-W true (λ ())
  -- --   Nat→NatW (suc n) = sup-W false (λ tt → Nat→NatW n)

  -- --   NatW→Nat : NatW → ℕ
  -- --   NatW→Nat (sup-W true x) = zero
  -- --   NatW→Nat (sup-W false x) = suc (NatW→Nat (x tt))

  -- --   invℕ : (n : ℕ) → NatW→Nat (Nat→NatW n) ≡ n
  -- --   invℕ zero = refl
  -- --   invℕ (suc n) = cong suc (invℕ n)

  -- --   invNatW : (x : NatW) → Nat→NatW (NatW→Nat x) ≡ x
  -- --   invNatW (sup-W true x) = cong (sup-W true) {!!}
  -- --   invNatW (sup-W false x) = cong (sup-W false) {!λ i tt → invNatW (x tt)!}

  -- --   doubleW : NatW → NatW
  -- --   doubleW (sup-W true x) = sup-W true x
  -- --   doubleW (sup-W false x) = sup-W false (λ _ → sup-W false (λ _ → sup-W true λ ()))

  -- --   W-elim : ∀ {S P} → (B : W S P → Type) → (Bsup-W : (s : S) → (f : P s → W S P) → B (sup-W s f)) → (w : W S P) → B w
  -- --   W-elim {S} {P} B Bsup-W (sup-W s x) = Bsup-W s x


  -- --   CoverW : (x y : W S P) → Type
  -- --   CoverW (sup-W s x) (sup-W s' x') = Σ (s ≡ s') (λ p → PathP (λ i → (P (p i) → W S P)) x x')

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
  -- --   decodeW {x = sup-W s x} {y = sup-W s' x'} (ps , px) = {! cong₂ sup-W ps px !}

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
