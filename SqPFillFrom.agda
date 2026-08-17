{-# OPTIONS --cubical=no-glue #-}

open import Helper

module SqPFillFrom where
  module _ where
    SqPFill : ∀{ℓ} (A : I → I → Type ℓ) → Type ℓ
    SqPFill A =
        {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
        {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
        (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
        → PathP (λ i → PathP (λ j → A i j) (a₋₀ i) (a₋₁ i)) a₀₋ a₁₋

    coe0→i : ∀{ℓ} {A : (i : I) → Type ℓ} → (i : I) → A i0 → A i
    coe0→i {A = A} i = transp (λ j → A (j ∧ i)) (~ i)

    coe1→i : ∀{ℓ} {A : (i : I) → Type ℓ} → (i : I) → A i1 → A i
    coe1→i {A = A} i =  transp (λ j → A ((~ j) ∨ i)) i

    coei→j : ∀{ℓ} {A : (i : I) → Type ℓ} → (i j : I) → A i → A j
    coei→j {A = A} i j = transport (λ k → A (if k then j else i end))

    -- from i to j via k
    icoe : (i j k : I) → I
    icoe i j k = if k then j else i end

    -- usually we have two lines: i to i' and j to j'
    -- from (i to i' via k) to (j to j' via k) via k'
    icoe2 : (i i' j j' k k' : I) → I
    icoe2 i i' j j' k k' = icoe (icoe i j k') (icoe i' j' k') k
    {- Discussion 07/08/2026 with Miguel, Yee-Jian, Andreas:
      It seems the following squares in I have the exact same boundary:
      λ k k' → icoe2 i  i' j  j' k  k'
                      |   X    |   X
      λ k k' → icoe2 i  j  i' j' k' k
    -}

    lemma : ∀{ℓ} (A : I → I → Type ℓ)
            {ilu jlu ild jld iru jru ird jrd : I}
            (lu : A ilu jlu)
            (ld : A ild jld)
            (l : PathP (λ k → A (icoe ilu ild k) (icoe jlu jld k)) lu ld)
            (ru : A iru jru)
            (rd : A ird jrd)
            (r : PathP (λ k → A (icoe iru ird k) (icoe jru jrd k)) ru rd)
            (u : PathP (λ k → A (icoe ilu iru k) (icoe jlu jru k)) lu ru)
            (d : PathP (λ k → A (icoe ild ird k) (icoe jld jrd k)) ld rd)
            (sqPFillA : SqPFill A)
            → PathP (λ i →
                PathP (λ j →
                -- these two formulations are definitionally equal.
                -- A (icoe2 ilu ild iru ird j i) (icoe2 jlu jru jld jrd i j)
                -- A (icoe (icoe ilu iru i) (icoe ild ird i) j) (icoe (icoe jlu jld j) (icoe jru jrd j) i)
                -- flipping the evaluation order gets us:
                -- A (icoe (icoe ilu iru i) (icoe ild ird i) j) (icoe (icoe jlu jru i) (icoe jld jrd i) j)
                A (icoe (icoe ilu ild j) (icoe iru ird j) i) (icoe (icoe jlu jru i) (icoe jld jrd i) j)
                ) (u i) (d i)) l r
    lemma {ℓ} A {ilu} {jlu} {ild} {jld} {iru} {jru} {ird} {jrd} lu ld l ru rd r u d sqPFillA ki kj = comp
        (λ k → A
        -- (icoe2 i0 i1 (icoe ilu iru ki) (icoe ild ird ki) kj k)
        (icoe2 i0 i1 (icoe ilu ild kj) (icoe iru ird kj) ki k)
        -- (icoe (icoe i0 i1 k) (icoe (icoe ilu iru ki) (icoe ild ird ki) k) kj)
        -- (icoe2 i0 i1 (icoe jlu jld kj) (icoe jru jrd kj) ki k))
        (icoe2 i0 i1 (icoe jlu jru ki) (icoe jld jrd ki) kj k))
        -- (icoe (icoe i0 i1 k) (icoe (icoe jlu jru ki) (icoe jld jrd ki) k) kj))
        -- (icoe ki (icoe (icoe ilu iru ki) (icoe ild ird ki) kj) k)
        -- (icoe kj (icoe2 jlu jru jld jrd ki kj) k))
        (λ where
        k (ki = i0) → lemmal (~ k) kj
        k (ki = i1) → lemmar (~ k) kj
        k (kj = i0) → lemmau (~ k) ki
        k (kj = i1) → lemmad (~ k) ki)
        (sq' ki kj)
        where
            lu't ru't ld't rd't : I → Type ℓ
            lu't = (λ k → A (icoe ilu i0 k) (icoe jlu i0 k))
            lu' : A i0 i0
            lu' = transport (λ k → lu't k) lu
            lemmalu : PathP lu't lu lu'
            lemmalu = transport-filler (λ k → lu't k) lu
            ru't = (λ k → A (icoe iru i1 k) (icoe jru i0 k))
            ru' : A i1 i0
            ru' = transport (λ k → ru't k) ru
            lemmaru : PathP ru't ru ru'
            lemmaru = transport-filler (λ k → ru't k) ru
            ld't = (λ k → A (icoe ild i0 k) (icoe jld i1 k))
            ld' : A i0 i1
            ld' = transport (λ k → ld't k) ld
            lemmald : PathP ld't ld ld'
            lemmald = transport-filler (λ k → ld't k) ld
            rd't = λ k → A (icoe ird i1 k) (icoe jrd i1 k)
            rd' : A i1 i1
            rd' = transport (λ k → rd't k) rd
            lemmard : PathP rd't rd rd'
            lemmard = transport-filler (λ k → rd't k) rd

            l't r't u't d't : I → I → Type ℓ
            l't kj k = A (icoe2 ilu ild i0 i0 kj k) (icoe2 jlu jld i0 i1 kj k)
            l' : PathP (λ j → A i0 j) lu' ld'
            l' kj = comp (λ k → l't kj k)
                        (λ where
                            k (kj = i0) → lemmalu k
                            k (kj = i1) → lemmald k) (l kj)
            lemmal : PathP (λ k → PathP (λ kj → l't kj k) (lemmalu k) (lemmald k)) l l'
            lemmal = transport-filler (λ k → PathP (λ kj → l't kj k) (lemmalu k) (lemmald k)) l

            r't kj k = A (icoe2 iru ird i1 i1 kj k) (icoe2 jru jrd i0 i1 kj k)
            r' : PathP (λ j → A i1 j) ru' rd'
            r' kj = comp (λ k → r't kj k)
                        (λ where
                            k (kj = i0) → lemmaru k
                            k (kj = i1) → lemmard k) (r kj)
            lemmar : PathP (λ k → PathP (λ kj → r't kj k) (lemmaru k) (lemmard k)) r r'
            lemmar = transport-filler (λ k → PathP (λ kj → r't kj k) (lemmaru k) (lemmard k)) r

            u't ki k = A (icoe2 ilu iru i0 i1 ki k) (icoe2 jlu jru i0 i0 ki k)
            u' : PathP (λ i → A i i0) lu' ru'
            u' ki = comp (λ k → u't ki k)
                        (λ where
                            k (ki = i0) → lemmalu k
                            k (ki = i1) → lemmaru k) (u ki)
            lemmau : PathP (λ k → PathP (λ ki → (u't ki k)) (lemmalu k) (lemmaru k)) u u'
            lemmau = transport-filler (λ k → PathP (λ ki → (u't ki k)) (lemmalu k) (lemmaru k)) u

            d't ki k = A (icoe2 ild ird i0 i1 ki k) (icoe2 jld jrd i1 i1 ki k)
            d' : PathP (λ i → A i i1) ld' rd'
            d' ki = comp (λ k → d't ki k)
                        (λ where
                            k (ki = i0) → lemmald k
                            k (ki = i1) → lemmard k) (d ki)
            lemmad : PathP (λ k → PathP (λ ki → d't ki k) (lemmald k) (lemmard k)) d d'
            lemmad = transport-filler (λ k → PathP (λ ki → d't ki k) (lemmald k) (lemmard k)) d

            sq' : PathP (λ i → PathP (λ j → A i j) (u' i) (d' i)) l' r'
            sq' = sqPFillA l' r' u' d'

    -- fromSqFill : ∀{ℓ} (A : I → I → Type ℓ) → ((i j : I) → SqFill (A i j)) → SqPFill A
    -- fromSqFill A sqFill {lu} {ld} l {ru} {rd} r u d i j = {! lemma A!}
      -- where
      --   coel : (coe0→i {A = λ _ → A i j} j lu) ≡ (coe1→i j ld)
      --   coel k = {!!}
