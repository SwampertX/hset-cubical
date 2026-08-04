{-# OPTIONS --cubical=no-glue #-}

open import Helper
open import SqFillDef
open import Agda.Builtin.Sigma

module SqFillSigma where
  module _ {ℓ ℓ'} (A : Type ℓ) (SqFillA : SqFill A) (B : A → Type ℓ') (SqFillB : (x : A) → SqFill (B x)) where
    SqFillSigma : SqFill (Σ A (λ a → B a))
    SqFillSigma {lu} {ld} l {ru} {rd} r u d i j .fst = SqFillA (cong fst l) (cong fst r) (cong fst u) (cong fst d) i j
    SqFillSigma {lu} {ld} l {ru} {rd} r u d i j .snd = outS (sqb i j)
        where
        sqa : Square (cong fst l) (cong fst r) (cong fst u) (cong fst d)
        sqa = SqFillA (cong fst l) (cong fst r) (cong fst u) (cong fst d)

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
        sqb' i' j' = inS (SqFillB (sqa i j) lb' rb' ub' db' i' j')

        sqb : (i' j' : I) → (B (sqa i' j')) [ ( i' ∨ ~ i' ∨ j' ∨ ~ j' ) ↦ sqb-hollow i' j' ]
        sqb i' j' = inS (comp (λ k → B (spread i j i' j' k)) (
                        λ where
                            k (i' = i0) → LemmaL (~ k) j'
                            k (i' = i1) → LemmaR (~ k) j'
                            k (j' = i0) → LemmaU (~ k) i'
                            k (j' = i1) → LemmaD (~ k) i') (outS (sqb' i' j')))

  {-# BUILTIN SQFILLSIGMA SqFillSigma #-}
