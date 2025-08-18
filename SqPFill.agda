-- If you are running mainline Agda, use --cubical
{-# OPTIONS --cubical=no-glue --type-in-type #-}

-- Prelude is glue-free: --cubical=no-glue works out of the box.
open import Cubical.Foundations.Prelude
  using (
    Level; Type; _≡_; refl; SquareP; PartialP;
    I; _∧_; _∨_; ~_; i0; i1; 1=1;
    Σ-syntax; fst; snd;
    cong; transport; PathP; transp; transport-filler; comp; Partial; _[_↦_]; inS; outS; hcomp;
    isProp; fromPathP; J; transportRefl; sym; congS
  )

module _ where
  sqFill : {ℓ : Level} → (A : I → I → Type ℓ) → Type ℓ
  sqFill A =
    {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
    {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
    (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
    → PathP (λ i → PathP (λ j → A i j) (a₋₀ i) (a₋₁ i)) a₀₋ a₁₋

  private postulate
    A A' : I → I → Type
    sqFillA : sqFill A
    sqFillA' : sqFill A'
    -- a b : A
    B : (i j : I) → A i j → Type
    sqFillB : (a : (i j : I) → A i j) → sqFill (λ i j → B i j (a i j))

  if_then_else_end : I → I → I → I
  if i then j else k end = (k ∧ (~ i ∨ j)) ∨ ((i ∨ k) ∧ j)

  {-# INLINE if_then_else_end #-}

  -- we cannot say (i = i') and (j = j').
  spread : (i j : I) → A i j → (i' j' : I) → A i' j'
  spread i j a i' j' = transport (λ k → A (if k then i' else i end) (if k then j' else j end)) a
  -- spread i j a i' j' = transp (λ k → A (if k then i' else i end) (if k then j' else j end)) (((i ∧ i') ∨ (~ i ∧ ~ i')) ∧ ((j ∧ j') ∨ (~ j ∧ ~ j'))) a

  ≡spread : (i j : I) (a : A i j) → a ≡ spread i j a i j
  -- ≡spread i j a = transport-filler (λ k → A (if k then i else i end) (if k then j else j end)) a
  ≡spread i j a k = transp (λ k' → A (if (k' ∧ k) then i else i end) (if (k' ∧ k) then j else j end)) (~ k) a
  -- ≡spread i j a k = transp (λ k' → A i j) (~ k) a
  -- ≡spread i j a k' = transp (λ k → A (if (k' ∧ k) then i else i end) (if (k' ∧ k) then j else j end)) (~ k' ∨ (((i ∧ i) ∨ (~ i ∧ ~ i)) ∧ ((j ∧ j) ∨ (~ j ∧ ~ j)))) a

  sqfillPiAB : sqFill (λ i j → (a : A i j) → B i j a)
  sqfillPiAB {ul} {dl} l {ur} {dr} r u d i j a =
    comp (λ k → congS (B i j) (sym (≡spread i j a)) k) {φ = i ∨ ~ i ∨ j ∨ ~ j}
      (λ where
        k (i = i0) → lemmaLB 1=1 (~ k)
        k (i = i1) → lemmaRB 1=1 (~ k)
        k (j = i0) → lemmaUB 1=1 (~ k)
        k (j = i1) → lemmaDB 1=1 (~ k)
          ) (b i j)
    where
      -- we spread any given (a : A i j) into a square
      sqa : (i' j' : I) → A i' j'
      sqa = spread i j a
      -- since we have a square of functions from (a : A i j) to (B i j a),
      -- we can then map sqa into B i j (sqa i j)
      -- in particular, we can have the corners in B
      ulb : B i0 i0 (sqa i0 i0)
      ulb = ul (sqa i0 i0)
      dlb : B i0 i1 (sqa i0 i1)
      dlb = dl (sqa i0 i1)
      urb : B i1 i0 (sqa i1 i0)
      urb = ur (sqa i1 i0)
      drb : B i1 i1 (sqa i1 i1)
      drb = dr (sqa i1 i1)
      -- sides in B
      lb : PathP (λ j → B i0 j (sqa i0 j)) ulb dlb
      lb j = l j (sqa i0 j)
      rb : PathP (λ j → B i1 j (sqa i1 j)) urb drb
      rb j = r j (sqa i1 j)
      ub : PathP (λ i → B i i0 (sqa i i0)) ulb urb
      ub i = u i (sqa i i0)
      db : PathP (λ i → B i i1 (sqa i i1)) dlb drb
      db i = d i (sqa i i1)
      -- and the filled square in (B i j (sqa i j)) by the sqfillB assumption.
      b : SquareP (λ i' j' → B i' j' (sqa i' j')) lb rb ub db
      b = sqFillB sqa lb rb ub db

      -- is this possible to hold definitionally?
      lemmaLB : PartialP (~ i) (λ {(i = i0) → PathP (λ k → B i j ((≡spread i j a) k)) (l j a) (lb j)})
      lemmaLB (i = i0) = λ k → l j (≡spread i j a k)
      lemmaRB : PartialP (  i) (λ {(i = i1) → PathP (λ k → B i j ((≡spread i j a) k)) (r j a) (rb j)})
      lemmaRB (i = i1) = λ k → r j (≡spread i j a k)
      lemmaUB : PartialP (~ j) (λ {(j = i0) → PathP (λ k → B i j ((≡spread i j a) k)) (u i a) (ub i)})
      lemmaUB (j = i0) = λ k → u i (≡spread i j a k)
      lemmaDB : PartialP (  j) (λ {(j = i1) → PathP (λ k → B i j ((≡spread i j a) k)) (d i a) (db i)})
      lemmaDB (j = i1) = λ k → d i (≡spread i j a k)

  sqfillSigmaAB : sqFill (λ i j → Σ[ a ∈ A i j ] B i j a)
  sqfillSigmaAB l r u d i j .fst = sqFillA (λ j → l j .fst) (λ j → r j .fst) (λ i → u i .fst) (λ i → d i .fst) i j
  sqfillSigmaAB l r u d i j .snd = sqFillB (λ i' j' → sqfillSigmaAB l r u d i' j' .fst)
                                           (λ j → l j .snd) (λ j → r j .snd) (λ i → u i .snd) (λ i → d i .snd) i j

  data cpd (A B : I → I → Type) (i j : I) : Type where
    inl : A i j → cpd A B i j
    inr : B i j → cpd A B i j

  data ⊥ : Type where

  ⊥-elim : {A : Type} (x : ⊥) → A
  ⊥-elim ()

  data ⊤ : Type where
    tt : ⊤

  inl≠inr : ∀ {A B : I → I → Type} {i j i' j' : I} (x : A i j) (y : B i' j') → (PathP (λ k → cpd A B (if k then i' else i end) (if k then j' else j end)) (inl x) (inr y)) → ⊥
  inl≠inr {A} {B} x y p = transport (λ k → isLeft (p k)) tt
    where
      isLeft : {i j : I} → cpd A B i j → Type
      isLeft (inl x) = ⊤
      isLeft (inr y) = ⊥

  Cover : {i j i' j' : I} (c : cpd A A' i j) (c' : cpd A A' i' j') → Type
  Cover {i} {j} {i'} {j'} (inl x) (inl y) = PathP (λ k → A (if k then i' else i end) (if k then j' else j end)) x y
  Cover {i} {j} {i'} {j'} (inr x) (inr y) = PathP (λ k → A' (if k then i' else i end) (if k then j' else j end)) x y
  Cover {i} {j} {i'} {j'} _ _ = ⊥

  reflCode : (i j : I) (c : cpd A A' i j) → Cover c c
  reflCode i j (inl x) = λ k → x
  reflCode i j (inr x) = λ k → x

  encode : {i j i' j' : I} {c : cpd A A' i j} {c' : cpd A A' i' j'} (p : PathP (λ k → cpd A A' (if k then i' else i end) (if k then j' else j end)) c c') → Cover c c'
  encode {i} {j} {i'} {j'} {c} p = transport (λ k → Cover c (p k)) (reflCode i j c)

  decode : {i j i' j' : I} {c : cpd A A' i j} {c' : cpd A A' i' j'} → Cover c c' → PathP (λ k → cpd A A' (if k then i' else i end) (if k then j' else j end)) c c'
  decode {c = inl x} {c' = inl y} p = λ k → inl (p k)
  decode {c = inr x} {c' = inr y} p = λ k → inr (p k)


  decodeEncode : {i j i' j' : I} {c : cpd A A' i j} {c' : cpd A A' i' j'}
                 (p : PathP (λ k → cpd A A' (if k then i' else i end) (if k then j' else j end)) c c')
                 → decode {c = c} {c' = c'} (encode p) ≡ p
  decodeEncode {i} {j} {i'} {j'} {c = inl x} {c'} p =
    transport
    (λ k → decode {c = inl x} {c' = p k} (encode {c = inl x} {c' = p k} (λ k' → p (k ∧ k'))) ≡ λ k' → p (k ∧ k'))
    (λ k → λ k' → inl (transportRefl (refl {x = x}) k k'))
  decodeEncode {c = inr x} {c'} p =
    transport
    (λ k → decode {c = inr x} {c' = p k} (encode {c = inr x} {c' = p k} (λ k' → p (k ∧ k'))) ≡ λ k' → p (k ∧ k'))
    (λ k → λ k' → inr (transportRefl (refl {x = x}) k k'))

  sqFillCoproduct : sqFill (cpd A A')
  sqFillCoproduct {inl lu} {inl ld} l {inl ru} {inl rd} r u d i j =
    (comp (λ k → cpd A A' i j)
      (λ where
        k (i = i0) → decodeEncode {c = l i0} {c' = l i1} l k j
        k (i = i1) → decodeEncode {c = r i0} {c' = r i1} r k j
        k (j = i0) → decodeEncode {c = u i0} {c' = u i1} u k i
        k (j = i1) → decodeEncode {c = d i0} {c' = d i1} d k i)
      (inl {A} {A'} (sqFillA
           (encode {c = l i0} {c' = l i1} l)
           (encode {c = r i0} {c' = r i1} r)
           (encode {c = u i0} {c' = u i1} u)
           (encode {c = d i0} {c' = d i1} d) i j)))
      -- {! inl {A} {A} (sqFillA (encode l) (encode r) (encode u) (encode d) i j) !}
  sqFillCoproduct {inr lu} {inr ld} l {inr ru} {inr rd} r u d i j =
    (comp (λ k → cpd A A' i j)
      (λ where
        k (i = i0) → decodeEncode {c = l i0} {c' = l i1} l k j
        k (i = i1) → decodeEncode {c = r i0} {c' = r i1} r k j
        k (j = i0) → decodeEncode {c = u i0} {c' = u i1} u k i
        k (j = i1) → decodeEncode {c = d i0} {c' = d i1} d k i)
      (inr {A} {A'} (sqFillA'
           (encode {c = l i0} {c' = l i1} l)
           (encode {c = r i0} {c' = r i1} r)
           (encode {c = u i0} {c' = u i1} u)
           (encode {c = d i0} {c' = d i1} d) i j)))
  sqFillCoproduct {inl x} {inr y} l _ _ _ = ⊥-elim (inl≠inr x y l)
  sqFillCoproduct {inr x} {inl y} l _ _ _ = ⊥-elim (inl≠inr y x (λ k → l (~ k)))
  sqFillCoproduct {inl x} {_} _ {inr y} _ u _ = ⊥-elim (inl≠inr x y u)
  sqFillCoproduct {inr x} {_} _ {inl y} _ u _ = ⊥-elim (inl≠inr y x (λ k → u (~ k)))
  sqFillCoproduct {_} {inl x} _ {_} {inr y} _ _ d = ⊥-elim (inl≠inr x y d)
  sqFillCoproduct {_} {inr x} _ {_} {inl y} _ _ d = ⊥-elim (inl≠inr y x (λ k → d (~ k)))

  -- from i to j via k
  icoe : (i j k : I) → I
  icoe i j k = if k then j else i end

  -- usually we have two lines: i to i' and j to j'
  -- from (i to i' via k) to (j to j' via k) via k'
  icoe2 : (i i' j j' k k' : I) → I
  icoe2 i i' j j' k k' = icoe (icoe i j k') (icoe i' j' k') k

  -- Given any i j i' j' square, we can always transport it to the 0 1 square, get a filling,
  -- and then hcomp it back to our
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
              -- these two formulations are definitionally equal.
              -- A (icoe2 ilu ild iru ird j i) (icoe2 jlu jru jld jrd i j)
              -- A (icoe (icoe ilu iru i) (icoe ild ird i) j) (icoe (icoe jlu jld j) (icoe jru jrd j) i)
              -- flipping the evaluation order gets us:
              -- A (icoe (icoe ilu iru i) (icoe ild ird i) j) (icoe (icoe jlu jru i) (icoe jld jrd i) j)
              A (icoe (icoe ilu ild j) (icoe iru ird j) i) (icoe (icoe jlu jru i) (icoe jld jrd i) j)
              ) (u i) (d i)) l r
  lemma {ilu} {jlu} {ild} {jld} {iru} {jru} {ird} {jrd} lu ld l ru rd r u d ki kj = comp
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

  -- Given any i j i' j' square, we can always transport it to the 0 1 square, get a filling,
  -- and then hcomp it back to our
  lemma' : {i j i' j' : I}
          (lu ld : A i j) (l : lu ≡ ld)
          (ru rd : A i' j') (r : ru ≡ rd)
          (u : PathP (λ k → A (icoe i i' k) (icoe j j' k)) lu ru)
          (d : PathP (λ k → A (icoe i i' k) (icoe j j' k)) ld rd)
          → PathP (λ ki → PathP (λ kj → A (icoe2 i i i' i' kj ki) (icoe2 j j' j j' ki kj)) (u ki) (d ki)) l r
  lemma' lu ld l ru rd r u d ki kj = lemma lu ld l ru rd r u d ki kj

  sqFillPath : (a b : (i j : I) → A i j) → sqFill (λ i j → a i j ≡ b i j)
  sqFillPath a b {lu} {ld} l {ru} {rd} r u d i j =
    comp (λ k → a (i ∧ k) (j ∧ k) ≡ b (i ∧ k) (j ∧ k))
      (λ where
        k (i = i0) → lemma' (a i0 i0) (b i0 i0) lu (a i0 j) (b i0 j) (l j) (λ k → a i0 (k ∧ j)) (λ k → b i0 (k ∧ j)) k
        k (i = i1) → lemma' (a i0 i0) (b i0 i0) lu (a i1 j) (b i1 j) (r j) (λ k → a k (k ∧ j)) (λ k → b k (k ∧ j)) k
        k (j = i0) → lemma' (a i0 i0) (b i0 i0) lu (a i i0) (b i i0) (u i) (λ k → a (k ∧ i) i0) (λ k → b (k ∧ i) i0) k
        k (j = i1) → lemma' (a i0 i0) (b i0 i0) lu (a i i1) (b i i1) (d i) (λ k → a (k ∧ i) k) (λ k → b (k ∧ i) k) k)
      lu
