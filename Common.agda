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

module Common (A : I → I → Type) where
  lemma : {ilu jlu ild jld iru jru ird jrd : I}
          (lu : A ilu jlu)
          (ld : A ild jld)
          (l : PathP (λ k → A (icoe ilu ild k) (icoe jlu jld k)) lu ld)
          (ru : A iru jru)
          (rd : A ird jrd)
          (r : PathP (λ k → A (icoe iru ird k) (icoe jru jrd k)) ru rd)
          (u : PathP (λ k → A (icoe ilu iru k) (icoe jlu jru k)) lu ru)
          (d : PathP (λ k → A (icoe ild ird k) (icoe jld jrd k)) ld rd)
          → PathP (λ i →
            PathP (λ j →
              A (icoe (icoe ilu ild j) (icoe iru ird j) i) (icoe (icoe jlu jru i) (icoe jld jrd i) j)
              ) (u i) (d i)) l r
  lemma {ilu} {jlu} {ild} {jld} {iru} {jru} {ird} {jrd} lu ld l ru rd r u d ki kj = comp
    (λ k → A
      (icoe2 i0 i1 (icoe ilu ild kj) (icoe iru ird kj) ki k)
      (icoe2 i0 i1 (icoe jlu jru ki) (icoe jld jrd ki) kj k))
    (λ where
       k (ki = i0) → lemmal (~ k) kj
       k (ki = i1) → lemmar (~ k) kj
       k (kj = i0) → lemmau (~ k) ki
       k (kj = i1) → lemmad (~ k) ki)
    (sq' ki kj)
      where
        lu't ru't ld't rd't : I → Type
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

        l't r't u't d't : I → I → Type
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
        sq' = sqFillA l' r' u' d'
