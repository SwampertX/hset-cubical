{-# OPTIONS --cubical=no-glue --termination-depth=100 #-}

open import SqFillDef
open import Helper


module SqFillW where

  data W {ℓS ℓP} (S : Type ℓS) (P : S → Type ℓP) : Type (ℓS ⊔ ℓP) where
    sup-W : (s : S) → (P s → W S P) → W S P

  module _ {ℓS ℓP} (S : Type ℓS) (P : S → Type ℓP) (sqFillS : SqFill S) (sqFillP : (s : S) → SqFill (P s)) where

    open import Agda.Builtin.Bool
    open import Agda.Builtin.Nat renaming (Nat to ℕ)
    open import Agda.Builtin.Sigma

    WtoΣ : W S P → Σ S (λ s → P s → W S P)
    WtoΣ (sup-W s x) = (s , x)

    ΣtoW : Σ S (λ s → P s → W S P) → W S P
    ΣtoW (s , x) = sup-W s x

    -- CoverS : (s s' : S) → Type ℓS
    -- CoverS = _≡_

    -- CoverP : {s s' : S} → CoverS s s' → Type ℓP
    -- CoverP cs = {!(p : P s) → !}

    CoverW : (w w' : W S P) → Type (ℓS ⊔ ℓP)
    -- CoverW (sup-W s x) (sup-W s' x') = Σ (s ≡ s') (λ p → PathP (λ i → (P (p i) → W S P)) x x')
    -- CoverW (sup-W s x) (sup-W s' x') = (s , x) ≡ (s' , x')
    CoverW (sup-W s x) (sup-W s' x') = (s , x) ≡ (s' , x')

    reflCodeW : {x : W S P} → CoverW x x
    -- reflCodeW {sup-W s x} = refl , refl
    reflCodeW {sup-W s x} = refl

    encodeW : {x y : W S P} → x ≡ y → CoverW x y
    -- encodeW {x} = J (λ y _ → CoverW x y) reflCodeW
    encodeW {x} = J (λ y _ → CoverW x y) reflCodeW

    encodeReflW : {x : W S P} → encodeW (refl {x = x}) ≡ reflCodeW {x = x}
    encodeReflW {x} = JRefl (λ y _ → CoverW x y) reflCodeW

    decodeW : {x y : W S P} → CoverW x y → x ≡ y
    -- decodeW {x = sup-W s x} {y = sup-W s' x'} (ps , px) = cong₂ sup-W ps px
    decodeW {x = sup-W s x} {y = sup-W s' x'} p = cong ΣtoW p

    decodeReflW : {w : W S P} → decodeW (encodeW (refl {x = w})) ≡ refl {x = w}
    -- decodeReflW {sup-W s x} i = cong₂ sup-W (encodeReflW {sup-W s x} i .fst) (encodeReflW {sup-W s x} i .snd)
    decodeReflW {sup-W s x} i = cong₂ sup-W (λ j → encodeReflW {sup-W s x} i j .fst) (λ j → encodeReflW {sup-W s x} i j .snd)

    encodeDecodeW : (x y : W S P) → (c : CoverW x y) → encodeW (decodeW c) ≡ c
    encodeDecodeW x y c = {!!}
    -- encodeDecodeW (sup-W s x) (sup-W s' x') (ps , px) = ?
    -- encodeDecodeW (sup-W s x) (sup-W s' x') p i = {!cong ()!}

    decodeEncodeW : {x y : W S P} → (p : x ≡ y) → decodeW (encodeW p) ≡ p
    -- decodeEncodeW {sup-W s x} {y} = J (λ y p → decodeW (encodeW p) ≡ p) decodeReflW
    decodeEncodeW {sup-W s x} {y} = J (λ y p → decodeW (encodeW p) ≡ p) decodeReflW

    SqFillW : SqFill (W S P)
    SqFillW {sup-W s00 x00} {sup-W s01 x01} w0- {sup-W s10 x10} {sup-W s11 x11} w1- w-0 w-1 i j =
        (hcomp (λ where
            k (i = i0) → decodeEncodeW w0- k j
            k (i = i1) → decodeEncodeW w1- k j
            k (j = i0) → decodeEncodeW w-0 k i
            k (j = i1) → decodeEncodeW w-1 k i)
          -- (sup-W (SquareΣ i j .fst) (SquareΣ i j .snd))
          -- (sup-W (sqs i j) λ ps → {!!})
          (decodeSquare encodeWFilledSquare i j)
        )
        where
          open import SqFillPi
          open import SqFillSigma

          -- sqs = sqFillS (λ i → encodeW w0- i .fst) (λ i → encodeW w1- i .fst) (λ i → encodeW w-0 i .fst) (λ i → encodeW w-1 i .fst)

          el : (s00 , x00) ≡ WtoΣ (sup-W s01 x01)
          el = encodeW w0-
          er : WtoΣ (sup-W s10 x10) ≡ WtoΣ (sup-W s11 x11)
          er = encodeW w1-
          eu : WtoΣ (sup-W s00 x00) ≡ WtoΣ (sup-W s10 x10)
          eu = encodeW w-0
          ed : WtoΣ (sup-W s01 x01) ≡ WtoΣ (sup-W s11 x11)
          ed = encodeW w-1


          decodeSquare : ∀{lu ld l ru rd r u d} → Square {A = Σ S (λ s → P s → W S P)} {lu} {ld} l {ru} {rd} r u d
            → Square (decodeW l) (decodeW r) (decodeW u) (decodeW d)
          decodeSquare {(lus , lux)} {l = l} {r = r} {u} {d} sq i j = ΣtoW (sq i j)

          fourSides : I → I → I
          fourSides i j = i ∨ ~ i ∨ j ∨ ~ j

          encodeWHollowSquare : (i j : I) → Partial (fourSides i j) (Σ S (λ s → P s → W S P))
          encodeWHollowSquare i j (i = i0) = (encodeW w0- j .fst , encodeW w0- j .snd)
          encodeWHollowSquare i j (i = i1) = (encodeW w1- j .fst , encodeW w1- j .snd)
          encodeWHollowSquare i j (j = i0) = (encodeW w-0 i .fst , encodeW w-0 i .snd)
          encodeWHollowSquare i j (j = i1) = (encodeW w-1 i .fst , encodeW w-1 i .snd)

          encodeWFilledSquare : Square {a₀₀ = (s00 , x00)} (encodeW w0-) (encodeW w1-) (encodeW w-0) (encodeW w-1)
          encodeWFilledSquare =
            -- SqFillSigma
            --   S sqFillS
            --   (λ s → P s → W S P)
            --   (λ s {lu} {ld} l r u d i j →
            --     SqFillPi
            --       (P s)
            --       (λ ps → W S P)
            --       (λ ps {lu} {ld} l r u d i j →
            --         SqFillW {lu} {ld} l r u d i j) {lu} l r u d i j) {(s00 , x00)} el er eu ed
            SqFillSigma
              S sqFillS
              (λ s → P s → W S P)
              (λ s {x'} l r u d i j ps →
                SqFillW {{!!}}
                        (λ j → l j ps) (λ j → r j ps) (λ i → u i ps) (λ i → d i ps) i j)
                {(s00 , x00)} el er eu ed

          -- encodeWFilledSquare i j .fst = sqFillS (cong fst el) (cong fst er) (cong fst eu) (cong fst ed) i j
          -- -- encodeWFilledSquare i j .snd = outS (sqb i j)
          -- encodeWFilledSquare i j .snd = SqFillPi (P (sqs i j)) (λ _ → W S P) (λ _ → SqFillW) {!cong snd el!} {!!} {!!} {!!} i j

          -- l' r' u' d' : I → Σ S (λ s → P s → W S P)
          -- l' j = (el j .fst , el j .snd)
          -- r' j = (er j .fst , er j .snd)
          -- u' i = (eu i .fst , eu i .snd)
          -- d' i = (ed i .fst , ed i .snd)

          -- SquareΣ : Square {encodeW w0-} (encodeW w1-) (encodeW w-0) (encodeW w-1)
          -- SquareΣ = SqFillSigma S sqFillS (λ s → P s → W S P)
          --   (λ s {pi00} {pi01} → SqFillPi (P s) (λ _ → W S P)
          --   (λ ps {w00} {w01} → SqFillW {{!pi00 ps!}} {w01}) {pi00} {pi01})
          --   (encodeW w0-) (encodeW w1-) (encodeW w-0) (encodeW w-1)
          -- spread : (i j i' j' : I) → sqs i j ≡ sqs i' j'
          -- spread i j i' j' k = sqs (if k then i' else i end) (if k then j' else j end)

          -- l = w0-
          -- r = w1-
          -- u = w-0
          -- d = w-1

          -- lu = sup-W s00 x00
          -- ld = sup-W s01 x01
          -- ru = sup-W s10 x10
          -- rd = sup-W s11 x11

          -- B : S → Type
          -- B s = P s → W S P

          -- lub : P (sqs i0 i0) → W S P
          -- lub = x00
          -- lub' : P (sqs i j) → W S P
          -- lub' = transport (λ k → B (spread i0 i0 i j k)) lub
          -- LemmaLU : PathP (λ k → B (spread i0 i0 i j k)) lub lub'
          -- LemmaLU k = transp (λ l → B (spread i0 i0 i j (k ∧ l))) (~ k) lub

          -- ldb : B (sqs i0 i1)
          -- ldb = x01
          -- ldb' : B (sqs i j)
          -- ldb' = transport (λ k → B (spread i0 i1 i j k)) ldb
          -- LemmaLD : PathP (λ k → B (spread i0 i1 i j k)) ldb ldb'
          -- LemmaLD k = transp (λ l → B (spread i0 i1 i j (k ∧ l))) (~ k) ldb

          -- lb : PathP (λ k → B (spread i0 i0 i0 i1 k)) lub ldb
          -- lb = cong snd (encodeW l)
          -- lb' : PathP (λ k → B (spread i j i j k)) lub' ldb'
          -- lb' j' = comp (λ k → B (spread (k ∧ i) (k ∧ j) (k ∧ i) (~ k ∨ j) j'))
          --                 (λ where
          --                 k (j' = i0) → LemmaLU k
          --                 k (j' = i1) → LemmaLD k) (lb j')
          -- LemmaL : PathP (λ k' → PathP (λ k → B (spread (k' ∧ i) (k' ∧ j) (k' ∧ i) (~ k' ∨ j) k)) (LemmaLU k') (LemmaLD k')) lb lb'
          -- LemmaL k' = transport-filler (λ k' → PathP (λ k → B (spread (k' ∧ i) (k' ∧ j) (k' ∧ i) (~ k' ∨ j) k)) (LemmaLU k') (LemmaLD k')) lb k'

          -- rub : B (sqs i1 i0)
          -- rub = x10
          -- rub' : B (sqs i j)
          -- rub' = transport (λ k → B (spread i1 i0 i j k)) rub
          -- LemmaRU : PathP (λ k → B (spread i1 i0 i j k)) rub rub'
          -- LemmaRU k = transp (λ l → B (spread i1 i0 i j (k ∧ l))) (~ k) rub

          -- rdb : B (sqs i1 i1)
          -- rdb = x11
          -- rdb' : B (sqs i j)
          -- rdb' = transport (λ k → B (spread i1 i1 i j k)) rdb
          -- LemmaRD : PathP (λ k → B (spread i1 i1 i j k)) rdb rdb'
          -- LemmaRD k = transp (λ l → B (spread i1 i1 i j (k ∧ l))) (~ k) rdb

          -- rb : PathP (λ j → B (sqs i1 j)) rub rdb
          -- rb = cong snd (encodeW r)
          -- rb' : rub' ≡ rdb'
          -- rb' j' = comp (λ k → B (spread (~ k ∨ i) (k ∧ j) (~ k ∨ i) (~ k ∨ j) j'))
          --                  (λ where
          --                  k (j' = i0) → LemmaRU k
          --                  k (j' = i1) → LemmaRD k) (rb j')
          -- LemmaR : PathP (λ k' → PathP (λ k → B (spread (~ k' ∨ i) (k' ∧ j) (~ k' ∨ i) (~ k' ∨ j) k)) (LemmaRU k') (LemmaRD k')) rb rb'
          -- LemmaR k' = transport-filler (λ k' → PathP (λ k → B (spread (~ k' ∨ i) (k' ∧ j) (~ k' ∨ i) (~ k' ∨ j) k)) (LemmaRU k') (LemmaRD k')) rb k'

          -- ub : PathP (λ i → B (sqs i i0)) lub rub
          -- ub = cong snd (encodeW u)
          -- ub' : lub' ≡ rub'
          -- ub' i' = comp (λ k → B (spread (k ∧ i) (k ∧ j) (~ k ∨ i) (k ∧ j) i'))
          --                  (λ where
          --                  k (i' = i0) → LemmaLU k
          --                  k (i' = i1) → LemmaRU k) (ub i')
          -- LemmaU : PathP (λ k' → PathP (λ k → B (spread (k' ∧ i) (k' ∧ j) (~ k' ∨ i) (k' ∧ j) k)) (LemmaLU k') (LemmaRU k')) ub ub'
          -- LemmaU k' = transport-filler (λ k' → PathP (λ k → B (spread (k' ∧ i) (k' ∧ j) (~ k' ∨ i) (k' ∧ j) k)) (LemmaLU k') (LemmaRU k')) ub k'

          -- db : PathP (λ i → B (sqs i i1)) ldb rdb
          -- db = cong snd (encodeW d)
          -- db' : ldb' ≡ rdb'
          -- db' i' = comp (λ k → B (spread (k ∧ i) (~ k ∨ j) (~ k ∨ i) (~ k ∨ j) i'))
          --                  (λ where
          --                  k (i' = i0) → LemmaLD k
          --                  k (i' = i1) → LemmaRD k) (db i')
          -- LemmaD : PathP (λ k' → PathP (λ k → B (spread (k' ∧ i) (~ k' ∨ j) (~ k' ∨ i) (~ k' ∨ j) k)) (LemmaLD k') (LemmaRD k')) db db'
          -- LemmaD k' = transport-filler (λ k' → PathP (λ k → B (spread (k' ∧ i) (~ k' ∨ j) (~ k' ∨ i) (~ k' ∨ j) k)) (LemmaLD k') (LemmaRD k')) db k'

          -- sqb-hollow : (i' j' : I) → Partial (i' ∨ j' ∨ ~ i' ∨ ~ j') (B (sqs i' j'))
          -- sqb-hollow i' j' (i' = i0) = (encodeW l) j' .snd
          -- sqb-hollow i' j' (i' = i1) = (encodeW r) j' .snd
          -- sqb-hollow i' j' (j' = i0) = (encodeW u) i' .snd
          -- sqb-hollow i' j' (j' = i1) = (encodeW d) i' .snd

          -- sqb'-hollow : (i' j' : I) → Partial (i' ∨ j' ∨ ~ i' ∨ ~ j') (B (sqs i j))
          -- sqb'-hollow i' j' (i' = i0) = lb' j'
          -- sqb'-hollow i' j' (i' = i1) = rb' j'
          -- sqb'-hollow i' j' (j' = i0) = ub' i'
          -- sqb'-hollow i' j' (j' = i1) = db' i'

          -- sqb' : (i' j' : I) → (B (sqs i j)) [ (i' ∨ j' ∨ ~ i' ∨ ~ j') ↦ sqb'-hollow i' j' ]
          -- -- sqb' i' j' = inS (SqFillB (sqs i j) lb' rb' ub' db' i' j')
          -- sqb' i' j' = inS (λ ps → SqFillW (λ j → lb' j ps) ((λ j → rb' j ps)) (λ i → ub' i ps) (λ i → db' i ps) i' j')

          -- sqb : (i' j' : I) → (B (sqs i' j')) [ ( i' ∨ ~ i' ∨ j' ∨ ~ j' ) ↦ sqb-hollow i' j' ]
          -- sqb i' j' = inS (comp (λ k → B (spread i j i' j' k)) (λ where
          --                   k (i' = i0) → LemmaL (~ k) j'
          --                   k (i' = i1) → LemmaR (~ k) j'
          --                   k (j' = i0) → LemmaU (~ k) i'
          --                   k (j' = i1) → LemmaD (~ k) i') (outS (sqb' i' j')))
