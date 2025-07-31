{-

Implementing computational UIP in Cubical Agda

Yee-Jian Tan

-}

{-
--cubical-ready (extra stuff for cubical), K-compatible
--cubical-without-glue, K-compatible

-}

-- {-# OPTIONS --cubical=full --type-in-type #-} -- the "normal" cubical agda
{-# OPTIONS --cubical --type-in-type #-} -- the "normal" cubical agda

-- open import Agda.Builtin.Cubical.Glue
open import Cubical.Foundations.Prelude
-- open import Cubical.Core.Primitives

-- refl : ∀ {A} {x : A} → x ≡ x
-- refl {x = x} _ = x
-- {-# INLINE refl #-}

-- transport : ∀ {A B} → A ≡ B → A → B
-- transport p a = transp (λ i → p i) i0 a

-- -- Transporting in a constant family is the identity function (up to a
-- -- path). If we would have regularity this would be definitional.
-- transportRefl : (x : A) → transport refl x ≡ x
-- transportRefl {A = A} x i = transp (λ _ → A) i x

-- transport-filler : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (x : A)
--                    → PathP (λ i → p i) x (transport p x)
-- transport-filler p x i = transp (λ j → p (i ∧ j)) (~ i) x

-- isSet : (A : Type) → Type
-- isSet A = (x y : A) (p q : x ≡ y) → p ≡ q

-- hcompRegularity : ∀ {A : Type} (a : A) → hcomp {A = a ≡ a} {φ = i1} (λ j _ → refl) refl ≡ refl
-- hcompRegularity a = refl

postulate uip : ∀ {i} (A : Type i) → isSet A

{-

Motivation:
- https://github.com/agda/agda/issues/3750 "A variant of Cubical Agda that is consistent with UIP" by NAD
- https://github.com/agda/agda/issues/6696 "Computational UIP in Agda Cubical" by Andreas Nuyts

A motivation: Joris Ceulemans was implementing Multimodal Type Theory (MTT) in Agda
syntax quotiented by equality - need nice QITs
needed functional extensionality

-}

-- crowdsourcing a nice small example?
data Circle : Type where
  base : Circle
  loop : base ≡ base

loop≡refl : loop ≡ refl
loop≡refl = uip Circle base base loop refl

{-

Current progress:
- Implemented a --cubical-without-glue flag: https://github.com/agda/agda/pull/7861 (under review) which fixes #3750
  Status: "yes" in principle, "blocked" by https://github.com/agda/agda/issues/7835

- TLDR of #7835: all structures in Cubical.Data.x includes Cubical.Data.x.Properties that contain glue (--cubical)
    thus incompatible with --erasure/--erased-cubical (unless manually erase all imported definitions)
    possible solution: separate Cubical library into --erased-cubical/--cubical-without-glue parts and --cubical parts?

- Here: implementing computational UIP.

  Now with a cubical variant that does not have Glue types (thus no univalence),
  it is possible to have UIP that computes.

  Q: First things first: is it consistent to have Cubical - Glue + (postulated) UIP?
  A: (Andreas Nuyts) There is trivially the Set model:
     - interval -> singleton
     - path types -> strict identity types (subsingleton sets that are inhabited iff both are equal)
     - transp and hcomp -> identity functions
     Translation to XTT (Sterling, Anguili, Gratzer 2020): Cubical + definitional UIP also possible.

  Q: What does it mean to "compute" UIP?
  A: Computation rules for UIP through type formers.
     For example, UIPA×B ≃ UIPA × UIPB
-}

{-
  Q: Which form of UIP do we implement?
  A: Recall that [UIP : (A : Type) → (a b : A) → (p q : a ≡ b) → p ≡ q]

     a ----p---- b
     |           |
     refl      refl
     |           |
     a ----q---- b

     says that the square above has a filler.

     It turns out that this is equivalent to saying that every square (or cube of dimension >= 2)
     has a filler:

     a00 ---a_0--- a10
      |             |
     a0_    aij    a1_
      |             |
     a01 ---a_1--- a11

     which "sounds" more general, hence easier to use. We are planning to implement this version.

-}




-- many relevant results are here, such that isOfHLevel×
open import Cubical.Foundations.HLevels

-- private variable
--     ℓ : Level
--     A A' : Type ℓ

-- -- taken from Cubical.Foundations.HLevels:
-- -- isSet→SquareP :
-- --   {A : I → I → Type ℓ}
-- --   (isSet : (i j : I) → isSet (A i j))
-- --   {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
-- --   {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
-- --   (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
-- --   → SquareP A a₀₋ a₁₋ a₋₀ a₋₁
-- -- isSet→SquareP isset a₀₋ a₁₋ a₋₀ a₋₁ =
-- --   PathPIsoPath _ _ _ .Iso.inv (isOfHLevelPathP' 1 (isset _ _) _ _ _ _ )

-- SquareP→isSet :
--   (squareP : {A : I → I → Type ℓ}
--     {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
--     {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
--     (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
--     → SquareP A a₀₋ a₁₋ a₋₀ a₋₁)
--   → (A : Type ℓ) → isSet A
-- SquareP→isSet squareP A a b p q = squareP p q refl refl

open import Data.Product hiding (Σ-syntax)

module _ where
  private postulate
    A : Type
    issetA : isSet A
    a b : A
    -- p q : a ≡ b
    B : A → Type
    issetB : (x : A) → isSet (B x)

  -- test : A
  -- test = transport refl a

  -- Test : Type
  -- Test = transport refl A

  issetPiAB : isSet ((x : A) → B x)
  issetPiAB f g p q i j x = issetB x (f x) (g x) (λ i → p i x) (λ i → q i x) i j

  issetSigmaAB : isSet (Σ[ a ∈ A ] B a)
  issetSigmaAB x y p q i j .fst = issetA (x .fst) (y .fst) (λ i → p i .fst) (λ i → q i .fst) i j
  issetSigmaAB x y p q i j .snd =
    -- isSet→SquareP : if you are locally isSet, ie given (A : I → I → Type), we have (isSetA : (i j : I) → isSet (A i j)),
    -- then we have the (heterogenous) sqFill property.
    -- even though our setting is homogenous, since sigma types are dependent,
    -- a homogenous shape [line, square, cube] in the first projection
    -- will give rise to a corresponding shape [line, square, cube] of types in the second projection.
    -- This forces us to give a PathP/SquareP in the second projection.
    isSet→SquareP (λ i j → issetB (issetSigmaAB x y p q i j .fst))
    (λ i → p i .snd) (λ i → q i .snd) refl refl i j
    -- issetB (issetSigmaAB x y p q i j .proj₁) {!transp (λ k → B ())!} {!!} {!!} {!!} i j

module SqFillNonDep where
  hSqFill : {ℓ : Level} → (A : Type ℓ) → Type ℓ
  hSqFill A =
    {a₀₀ : A} {a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
    {a₁₀ : A} {a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
    (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
    → Square a₀₋ a₁₋ a₋₀ a₋₁

  private postulate
    A : Type
    hSqFillA : hSqFill A
    a b : A
    B : A → Type
    hSqFillB : (x : A) → hSqFill (B x)

  hSqFillProductAB : hSqFill (A × A)
  hSqFillProductAB l r u d i j .fst = hSqFillA (cong fst l) (cong fst r) (cong fst u) (cong fst d) i j
  hSqFillProductAB l r u d i j .snd = hSqFillA (λ i → l i .snd) (λ i → r i .snd) (λ i → u i .snd) (λ i → d i .snd) i j

  hSqFillPiAB : hSqFill ((a : A) → B a)
  hSqFillPiAB l r u d i j a = hSqFillB a (λ i → l i a) (λ i → r i a) (λ i → u i a) (λ i → d i a) i j

  if_then_else_end : I → I → I → I
  -- this is the one that compiles to j or k when i is i0 or i1
  -- if i then j else k end = ((~ i) ∧ k) ∨ (i ∧ j)
  -- if i then j else k end = (k ∨ i) ∧ (j ∨ ~ i)
  -- if i then j else k end = (k ∧ ~ i) ∨ ((i ∨ k) ∧ j)
  if i then j else k end = (k ∧ (~ i ∨ j)) ∨ (i ∧ j)
  -- if i then j else k end = (i ∨ k) ∧ (j ∨ ~ i)

  if1_then_else_end : I → I → I → I
  -- this is the one that compiles to j or k when j = k.
  if1 i then j else k end = (k ∧ (~ i ∨ j)) ∨ ((i ∨ k) ∧ j)

  -- is it possible to have both?
  if'_then_else_end : I → I → I → I
  if' i then j else k end = (k ∧ (~ i ∨ j)) ∨ ((i ∨ k) ∧ j) ∨ ((~ i) ∧ k) ∨ (i ∧ j)

  {-# INLINE if_then_else_end #-}

  -- test : I → I → I
  -- test i j = {!if i then j else j end!}

  {-
  spread : (i j : I) → A i j → (i' j' : I) → A i' j'
  spread i j a i' j' = transport (λ k → A (if k then i' else i end) (if k then j' else j end)) a

  -- not provable because I is only a de morgan algebra.
  -- in particular, (~ k ∨ i) ∧ (k ∨ i) ≠ i.
  ≡spread : (i j : I) (a : A i j) → a ≡ spread i j a i j
  ≡spread i j a = transport-filler (λ k → A (if k then i else i end) (if k then j else j end)) a
  -}

  sqfillSigmaAB : hSqFill (Σ[ a ∈ A ] B a)
  sqfillSigmaAB l r u d i j .fst = hSqFillA (cong fst l) (cong fst r) (cong fst u) (cong fst d) i j
  sqfillSigmaAB {lu} {ld} l {ru} {rd} r u d i j .snd =
    hSqFillB (sqfillSigmaAB l r u d i j .proj₁)
      {a₀₀ = lub'} {a₀₁ = ldb'} lb' {a₁₀ = rub'} {a₁₁ = rdb'} rb' ub' db' i {!j!}
    where
      sqa : Square (cong fst l) (cong fst r) (cong fst u) (cong fst d)
      sqa = hSqFillA (cong fst l) (cong fst r) (cong fst u) (cong fst d)

      -- coe0i : (A : Type) (x y : A) (i : I) (p : x ≡ y) → x ≡ p i
      -- coe0i A x y i p j = p (if j then i else i0 end)

      spread : (i j i' j' : I) → sqa i j ≡ sqa i' j'
      -- spread i j i' j' k = sqa (if1 k then i' else i end) (if1 k then j' else j end)
      spread i j i' j' k = sqa (if k then i' else i end) (if k then j' else j end)
      -- spread i j i' j' k = sqa (if' k then i' else i end) (if' k then j' else j end)

      -- spreadRegular : (i j : I) → spread i j i j ≡ refl
      -- spreadRegular i j = refl

      lub : B (sqa i0 i0)
      lub = snd lu
      lub' : B (sqa i j)
      -- lub' = transport (λ k → B (spread i0 i0 i j k)) lub
      -- lub' = transport (λ k → B (sqa (i ∧ k) (j ∧ k))) lub
      lub' = transp (λ k → B (spread i0 i0 i j k)) (~ i ∧ ~ j) lub
      -- lub' = transp (λ k → B (spread i0 i0 i j k)) (~ i ∧ ~ j) lub
      LemmaLU : PathP (λ k → B (spread i0 i0 i j k)) lub lub'
      LemmaLU k = transp (λ l → B (spread i0 i0 i j (k ∧ l))) (~ k ∨ (~ i ∧ ~ j)) lub

      ldb : B (fst ld)
      ldb = snd ld
      ldb' : B (sqa i j)
      -- ldb' = transport (λ k → B (sqa (i ∧ k) (~ k ∨ j))) ldb
      ldb' = transp (λ k → B (spread i0 i1 i j k)) (~ i ∧ j) ldb
      LemmaLD : PathP (λ k → B (spread i0 i1 i j k)) ldb ldb'
      LemmaLD k = transp (λ l → B (spread i0 i1 i j (k ∧ l))) (~ k ∨ (~ i ∧ j)) ldb

      lb : PathP (λ j → B (sqa i0 j)) lub ldb
      lb = cong snd l
      lb' : lub' ≡ ldb'
      lb' j' = transp (λ k → B (spread i0 j' i j k)) (~ i ∧ (if  j' then j else ~ j end)) (lb j')
      -- lb' j' = transp (λ k → B (spread i0 j' i j k)) (~ i) (lb j')

      rub : B (fst ru)
      rub = snd ru
      rub' : B (sqa i j)
      rub' = transp (λ k → B (spread i1 i0 i j k)) (i ∧ ~ j) rub
      LemmaRU : PathP (λ k → B (spread i1 i0 i j k)) rub rub'
      LemmaRU k = transp (λ l → B (spread i1 i0 i j (k ∧ l))) (~ k ∨ ( i ∧ ~ j)) rub

      rdb : B (fst rd)
      rdb = snd rd
      rdb' : B (sqa i j)
      rdb' = transp (λ k → B (spread i1 i1 i j k)) (i ∧ j) rdb
      LemmaRD : PathP (λ k → B (spread i1 i1 i j k)) rdb rdb'
      LemmaRD k = transp (λ l → B (spread i1 i1 i j (k ∧ l))) (~ k ∨ ( i ∧   j)) rdb

      rb : PathP (λ j → B (sqa i1 j)) rub rdb
      rb = cong snd r
      rb' : rub' ≡ rdb'
      rb' j' = transp (λ k → B (spread i1 j' i j k)) (i ∧ (if  j' then j else ~ j end)) (rb j')

      ub : PathP (λ i → B (sqa i i0)) lub rub
      ub = cong snd u
      ub' : lub' ≡ rub'
      ub' i' = transp (λ k → B (spread i' i0 i j k)) ((if  i' then i else ~ i end) ∧ ~ j) (ub i')

      db : PathP (λ i → B (sqa i i1)) ldb rdb
      db = cong snd d
      db' : ldb' ≡ rdb'
      db' i' = transp (λ k → B (spread i' i1 i j k)) ((if  i' then i else ~ i end) ∧ j) (db i')

      {-
        lub'
         |  \ transport filler
         |   lub
     lb' |    | lb
         |   ldb
         |  / transport filler
        ldb'
        we need a comp!
      -}
      -- lb' : lub' ≡ ldb'
      -- -- lb' i' = comp (λ k → B (sqa (if1 k then i else i0 end) (if1 k then j else i' end))) (λ{
      -- lb' j' = comp (λ k → B (spread i0 j' i j k)) (λ{
      --     k (j' = i0) → LemmaLU k ;
      --     k (j' = i1) → LemmaLD k
      --   }) (lb j')

      -- rb' : rub' ≡ rdb'
      -- rb' j' = comp (λ k → B (spread i1 j' i j k)) (λ{
      --     k (j' = i0) → LemmaRU k ;
      --     k (j' = i1) → LemmaRD k
      --   }) (rb j')

      -- ub' : lub' ≡ rub'
      -- ub' i' = comp (λ k → B (spread i' i0 i j k)) (λ{
      --     j' (i' = i0) → LemmaLU j' ;
      --     j' (i' = i1) → LemmaRU j'
      --   }) (ub i')

      -- db' : ldb' ≡ rdb'
      -- -- db' i' = comp (λ k → B (sqa (if k then i else i' end) (~ k ∨ j))) (λ{
      -- db' i' = comp (λ k → B (spread i' i1 i j k)) (λ{
      --     j' (i' = i0) → LemmaLD j' ;
      --     j' (i' = i1) → LemmaRD j'
      --   }) (db i')

      sqb' : B (sqa i j)
      sqb' = hSqFillB (sqfillSigmaAB l r u d i j .fst) {a₀₀ = lub'} {a₀₁ = ldb'} lb' {a₁₀ = rub'} {a₁₁ = rdb'} rb' ub' db' i j

      -- eg: when i = j = i0, a : A i0 i0 should be path-equivalent to sqa i0 i0
      -- lemmaUL : PartialP (~ i ∧ ~ j) (λ{(i = i0) (j = i0) → a ≡ sqa i j})
      -- lemmaUL (i = i0) (j = i0) = transport-filler _ a
      -- lemmaDL : PartialP (~ i ∧   j) (λ{(i = i0) (j = i1) → a ≡ sqa i j})
      -- lemmaDL (i = i0) (j = i1) = transport-filler _ a
      -- lemmaUR : PartialP (  i ∧ ~ j) (λ{(i = i1) (j = i0) → a ≡ sqa i j})
      -- lemmaUR (i = i1) (j = i0) = transport-filler _ a
      -- lemmaDR : PartialP (  i ∧   j) (λ{(i = i1) (j = i1) → a ≡ sqa i j})
      -- lemmaDR (i = i1) (j = i1) = transport-filler _ a

      -- lemmaL : PartialP (~ i) (λ {(i = i0) → a ≡ sqa i j})
      -- lemmaL (i = i0) = ≡spread i j a

      -- their spread i j i' j' : A i j → A i' j'
      -- ≡spread i j a : a ≡ spread i j i j a
      -- lemmaLB : PartialP (~ i) (λ {(i = i0) → lb j ≡ lb' j})
      -- lemmaLB (i = i0) = λ k → {!!}
      -- lemmaLB (i = i0) = λ k → {!!}
      -- lemmaLB (i = i0) = λ k → transp (λ l → B (spread i (k ∧ l) i j (k ∧ l))) (~ k ∨ (~ i ∧ (if l then ~ j else j end))) ldb
      -- lemmaRB : PartialP (  i) (λ {(i = i1) → PathP (λ k → B i j ((≡spread i j a) k)) (r j a) (rb j)})
      -- lemmaRB (i = i1) = λ k → r j (≡spread i j a k)
      -- lemmaUB : PartialP (~ j) (λ {(j = i0) → PathP (λ k → B i j ((≡spread i j a) k)) (u i a) (ub i)})
      -- lemmaUB (j = i0) = λ k → u i (≡spread i j a k)
      -- lemmaDB : PartialP (  j) (λ {(j = i1) → PathP (λ k → B i j ((≡spread i j a) k)) (d i a) (db i)})
      -- lemmaDB (j = i1) = λ k → d i (≡spread i j a k)

  --   -- either we fill the general square at B (αij) for any i j (we need to transport wiggle each side up to i,j)
  --   sqfillB (sqfillSigmaAB l r u d i j .proj₁) {!fromPathP (cong snd l)!} {!!} {!!} {!!} i {!!}
  --   -- or first wiggle our square to the comfortable transatlantic position and fill in the sides.
  --   -- toPathP (toPathP {!!}) i

  -- here we recreate the isOfHLevelΣ proof from the HLevels file, but here for the hSqFill property instead.
  -- Idea: To show the hSqFill property for the Sigma type,
  -- it suffices to take an empty square in the Sigma type and give it a filling.
  -- To give a filling in a Sigma type is to give fillings in the two projections.
  -- 1. A filling in the first projection is easy: we can direcly apply the hSqFillA assumption.
  -- 2. A filling in the second projection is tricky because the square is HETEROGENOUS.
  --    Why? Because Sigma type depends on the first projection, and the first projection is a square.
  --    In other words, we need to give a PathP from say l to r in the second projection.
  -- 3. Here we use two intermediate, standard results about paths:
  --    i. (PathP A x y) is isomorphic to (transport A x ≡ y).
  --       So instead of giving a (PathP _ l r), we can give a (transport _ l ≡ r).
  --       In particular, we don't need the whole isomorphism: we merely need a way to go TO PathP from Path.
  --    ii. It remains to provide a (transport _ l ≡ r), a homogenous equality in the ambient type (PathP (A i1) ru rd).
  --        This can be done by noting that if a type A has h-level (suc n), then its path space has h-level n.
  --        In particular,
  --        - the type of the endpoint of (PathP (A i1) ru rd), (A i1 i1) has sqfill (by our assumption) so is a set, and
  --        - thus the Path type (PathP (A i1) ru rd) is a prop.
  --        - now supply (transport _ l) and r, we get an equality between them.
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

  inl≠inr : ∀ A B (x : A) (y : B) → (inl x ≡ inr y) → ⊥
  inl≠inr A B x y p = transport (cong isLeft p) tt
    where
      isLeft : (A + B) → Type
      isLeft (inl x) = ⊤
      isLeft (inr y) = ⊥

  Cover : (c c' : A + A) → Type
  Cover (inl x) (inl y) = x ≡ y
  Cover (inr x) (inr y) = x ≡ y
  Cover _ _ = ⊥

  reflCode : (c : A + A) → Cover c c
  reflCode (inl x) = refl
  reflCode (inr x) = refl

  encode : {c c' : A + A} → c ≡ c' → Cover c c'
  -- encode {c} = J (λ c' _ → Cover c c') (reflCode c)
  encode {c} p = transport (λ i → Cover c (p i)) (reflCode c)

  decode : {c c' : A + A} → Cover c c' → c ≡ c'
  decode {inl x} {inl y} = cong inl
  decode {inr x} {inr y} = cong inr
  -- decode {inl x} {inl y} = J (λ y _ → inl x ≡ inl y) refl
  -- decode {inr x} {inr y} = J (λ y _ → inr x ≡ inr y) refl

  decodeEncode : {c c' : A + A} (p : c ≡ c') → decode (encode p) ≡ p
  decodeEncode {inl x} = J (λ c' p → decode (encode p) ≡ p) (cong (cong inl) (transportRefl refl))
  decodeEncode {inr x} = J (λ c' p → decode (encode p) ≡ p) (cong (cong inr) (transportRefl refl))

  -- TODO: this has the right type already (A + A) but boundary conditions are off
  -- i.e. [inl (encode l j)] and [l j] are only propositionally equal.
  -- Solution: hcomp [sqa] to have the right type.
  -- sqa : (i j : I) → (A + A) [ (i ∨ ~ i ∨ j ∨ ~ j) ↦ (λ where
  --   -- (i = i0) → l j
  --   -- (i = i1) → r j
  --   -- (j = i0) → u i
  --   -- (j = i1) → d i) ]
  --     (i = i0) → inl (encode l j)
  --     (i = i1) → inl (encode r j)
  --     (j = i0) → inl (encode u i)
  --     (j = i1) → inl (encode d i))
  --   ]
  -- sqa i j = inS (inl {A} {A} (hSqFillA (encode l) (encode r) (encode u) (encode d) i j))

  -- lemmal : l ≡ cong inl (encode l)
  -- lemmal = sym (decodeEncode l)

  -- sqa' : (i j : I) → (A + A) [ (i ∨ ~ i ∨ j ∨ ~ j) ↦ (λ where
  --     (i = i0) → l j
  --     (i = i1) → r j
  --     (j = i0) → u i
  --     (j = i1) → d i
  --   )]
  -- sqa' i j = inS (hcomp (λ where
  --     k (i = i0) → decodeEncode l k j
  --     k (i = i1) → decodeEncode r k j
  --     k (j = i0) → decodeEncode u k i
  --     k (j = i1) → decodeEncode d k i)
  --   (inl {A} {A} (hSqFillA (encode l) (encode r) (encode u) (encode d) i j)))

  hSqFillCoproduct : hSqFill (A + A)
  hSqFillCoproduct {inl lu} {inl ld} l {inl ru} {inl rd} r u d i j =
    -- outS (sqa' i j)
    (hcomp (λ where
        k (i = i0) → decodeEncode l k j
        k (i = i1) → decodeEncode r k j
        k (j = i0) → decodeEncode u k i
        k (j = i1) → decodeEncode d k i)
      (inl {A} {A} (hSqFillA (encode l) (encode r) (encode u) (encode d) i j)))
  hSqFillCoproduct {inr lu} {inr ld} l {inr ru} {inr rd} r u d i j =
    (hcomp (λ where
        k (i = i0) → decodeEncode l k j
        k (i = i1) → decodeEncode r k j
        k (j = i0) → decodeEncode u k i
        k (j = i1) → decodeEncode d k i)
      (inr {A} {A} (hSqFillA (encode l) (encode r) (encode u) (encode d) i j)))
  hSqFillCoproduct {inl x} {inr y} l _ _ _ = ⊥-elim (inl≠inr A A x y l)
  hSqFillCoproduct {inr x} {inl y} l _ _ _ = ⊥-elim (inl≠inr A A y x (sym l))
  hSqFillCoproduct {inl x} {_} _ {inr y} _ u _ = ⊥-elim (inl≠inr A A x y u)
  hSqFillCoproduct {inr x} {_} _ {inl y} _ u _ = ⊥-elim (inl≠inr A A y x (sym u))
  hSqFillCoproduct {_} {inl x} _ {_} {inr y} _ _ d = ⊥-elim (inl≠inr A A x y d)
  hSqFillCoproduct {_} {inr x} _ {_} {inl y} _ _ d = ⊥-elim (inl≠inr A A y x (sym d))
  -- hSqFillCoproduct {_} {_} _ {inl x} {inr y} r _ _ = ⊥-elim (inl≠inr A A x y r)
  -- hSqFillCoproduct {_} {_} _ {inr x} {inl y} r _ _ = ⊥-elim (inl≠inr A A y x (sym r))

  lineToPathP : (A : I → Type) → Type
  lineToPathP A = PathP (λ i → Type) (A i0) (A i1)

  PathPToLine : ∀ A B → (P : PathP (λ i → Type) A B) → I → Type
  PathPToLine A B P i = P i

  -- hSqFillPath : {a : A} → hSqFill (a ≡ a)
  -- hSqFillPath {a} {lu} {ld} l {ru} {rd} r u d i j =
  --   hcomp (λ k → λ { (i = i0) → hSqFillA lu (l j) refl refl k
  --                 ; (i = i1) → hSqFillA lu (r j) refl refl k
  --                 ; (j = i0) → hSqFillA lu (u i) refl refl k
  --                 ; (j = i1) → hSqFillA lu (d i) refl refl k}) lu
  hSqFillPath : {a b : A} → hSqFill (a ≡ b)
  hSqFillPath {_} {_} {lu} l r u d i j =
    hcomp (λ k → λ { (i = i0) → hSqFillA lu (l j) refl refl k
                  ; (i = i1) → hSqFillA lu (r j) refl refl k
                  ; (j = i0) → hSqFillA lu (u i) refl refl k
                  ; (j = i1) → hSqFillA lu (d i) refl refl k}) lu
    -- where
    --   h : isProp (a ≡ a)
    --   h x y i j = hSqFillA x y refl refl i j


module _ where
  sqFill : {ℓ : Level} → (A : I → I → Type ℓ) → Type ℓ
  sqFill A =
    {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
    {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
    (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
    → SquareP A a₀₋ a₁₋ a₋₀ a₋₁

  private postulate
    A : I → I → Type
    sqFillA : sqFill A
    -- a b : A
    B : (i j : I) → A i j → Type
    sqFillB : (a : (i j : I) → A i j) → sqFill (λ i j → B i j (a i j))

  -- sqfillProductAB : sqFill (λ _ _ → A × A)
  -- sqfillProductAB l r u d i j .fst = sqfillA (cong fst l) (cong fst r) (cong fst u) (cong fst d) i j
  -- sqfillProductAB l r u d i j .snd = sqfillA (λ i → l i .snd) (λ i → r i .snd) (λ i → u i .snd) (λ i → d i .snd) i j
  --
  if_then_else_end : I → I → I → I
  -- if k then i else j end = ((~ k) ∧ j) ∨ (k ∧ i)
  -- if k then i else j end = (j ∨ ~ k) ∧ (i ∨ k)
  if i then j else k end = (k ∧ ~ i) ∨ ((i ∨ k) ∧ j)
  -- if i then j else k end = (k ∧ (~ i ∨ j)) ∨ ((i ∨ k) ∧ j)

  {-# INLINE if_then_else_end #-}

  spread : (i j : I) → A i j → (i' j' : I) → A i' j'
  spread i j a i' j' = transport (λ k → A (if k then i' else i end) (if k then j' else j end)) a

  -- not provable because I is only a de morgan algebra.
  -- in particular, (~ k ∨ i) ∧ (k ∨ i) ≠ i.
  ≡spread : (i j : I) (a : A i j) → a ≡ spread i j a i j
  ≡spread i j a = transport-filler (λ k → A (if k then i else i end) (if k then j else j end)) a

  -- spread' : (i j : I) → A i j → (i' j' : I) → A i' j'
  -- spread' i j a i' j' = {!!}

  sqfillPiAB : sqFill (λ i j → (a : A i j) → B i j a)
  sqfillPiAB {ul} {dl} l {ur} {dr} r u d i j a =
    -- comp (λ k → congS (B i j) (sym (≡spread i j a)) k) {φ = i ∨ ~ i ∨ j ∨ ~ j}
    --   (λ where
    --     k (i = i0) → lemmaLB 1=1 (~ k)
    --     k (i = i1) → lemmaRB 1=1 (~ k)
    --     k (j = i0) → lemmaUB 1=1 (~ k)
    --     k (j = i1) → lemmaDB 1=1 (~ k)
    --       ) (b i j)
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

      -- now we have a square in (λ i' j' → B i' j' (sqa i' j'))
      -- but it is not definitionally the square we want: (B i j a)
      -- a and (sqa i j) are path equivalent: sqa is obtained via transporting a.
      -- we prove these equalities below.

      -- eg: when i = j = i0, a : A i0 i0 should be path-equivalent to sqa i0 i0
      -- lemmaUL : PartialP (~ i ∧ ~ j) (λ{(i = i0) (j = i0) → a ≡ sqa i j})
      -- lemmaUL (i = i0) (j = i0) = transport-filler _ a
      -- lemmaDL : PartialP (~ i ∧   j) (λ{(i = i0) (j = i1) → a ≡ sqa i j})
      -- lemmaDL (i = i0) (j = i1) = transport-filler _ a
      -- lemmaUR : PartialP (  i ∧ ~ j) (λ{(i = i1) (j = i0) → a ≡ sqa i j})
      -- lemmaUR (i = i1) (j = i0) = transport-filler _ a
      -- lemmaDR : PartialP (  i ∧   j) (λ{(i = i1) (j = i1) → a ≡ sqa i j})
      -- lemmaDR (i = i1) (j = i1) = transport-filler _ a

      -- lemmaL : PartialP (~ i) (λ {(i = i0) → a ≡ sqa i j})
      -- lemmaL (i = i0) = ≡spread i j a

      lemmaLB : PartialP (~ i) (λ {(i = i0) → PathP (λ k → B i j ((≡spread i j a) k)) (l j a) (lb j)})
      lemmaLB (i = i0) = λ k → l j (≡spread i j a k)
      lemmaRB : PartialP (  i) (λ {(i = i1) → PathP (λ k → B i j ((≡spread i j a) k)) (r j a) (rb j)})
      lemmaRB (i = i1) = λ k → r j (≡spread i j a k)
      lemmaUB : PartialP (~ j) (λ {(j = i0) → PathP (λ k → B i j ((≡spread i j a) k)) (u i a) (ub i)})
      lemmaUB (j = i0) = λ k → u i (≡spread i j a k)
      lemmaDB : PartialP (  j) (λ {(j = i1) → PathP (λ k → B i j ((≡spread i j a) k)) (d i a) (db i)})
      lemmaDB (j = i1) = λ k → d i (≡spread i j a k)

      -- lemmaB : PartialP


    -- transport {!PathP!} (sqfillB (spread i j a)
    -- (λ k → l k (transp (λ i' → A (if i' then i else i0 end) (if i' then j else k end)) i0 a))
    -- (λ k → r k (transp (λ i' → A (if i' then i else i1 end) (if i' then j else k end)) i0 a))
    -- (λ k → u k (transp (λ i' → A (if i' then i else k end) (if i' then j else i0 end)) i0 a))
    -- (λ k → d k (transp (λ i' → A (if i' then i else k end) (if i' then j else i1 end)) i0 a))
    -- )
    -- sqfillB (λ i' j' → transport {!refl!} (spread i j a i' j')) {!!} {!!} {!!} {!!} {!!} {!!}


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

  -- inl≠inr : ∀ {A B : I → I → Type} {i j i' j' : I} (x : A i j) (y : B i' j') → (PathP (λ k → cpd A B ((k ∨ i) ∧ (~ k ∨ i')) ((k ∨ j) ∧ (~ k ∨ j'))) (inl x) (inr y)) → ⊥
  inl≠inr : ∀ {A B : I → I → Type} {i j i' j' : I} (x : A i j) (y : B i' j') → (PathP (λ k → cpd A B (if k then i' else i end) (if k then j' else j end)) (inl x) (inr y)) → ⊥
  inl≠inr {A} {B} x y p = transport (λ k → isLeft (p k)) tt
    where
      isLeft : {i j : I} → cpd A B i j → Type
      isLeft (inl x) = ⊤
      isLeft (inr y) = ⊥

  -- Cover' : (i j i' j' : I) (c : cpd A A i j) (c' : cpd A A i' j') → Type
  -- Cover' i j i' j' (inl x) (inl y) = PathP (λ k → A (if k then i' else i end) (if k then j' else j end)) x y
  -- Cover' i j i' j' (inr x) (inr y) = PathP (λ k → A (if k then i' else i end) (if k then j' else j end)) x y
  -- Cover' i j i' j' _ _ = ⊥

  Cover : {i j i' j' : I} (c : cpd A A i j) (c' : cpd A A i' j') → Type
  Cover {i} {j} {i'} {j'} (inl x) (inl y) = PathP (λ k → A (if k then i' else i end) (if k then j' else j end)) x y
  Cover {i} {j} {i'} {j'} (inr x) (inr y) = PathP (λ k → A (if k then i' else i end) (if k then j' else j end)) x y
  Cover {i} {j} {i'} {j'} _ _ = ⊥

  reflCode : (i j : I) (c : cpd A A i j) → Cover c c
  reflCode i j (inl x) = λ k → x
  reflCode i j (inr x) = λ k → x

  if'_then_else_end : I → I → I → I
  -- if' i then j else k end = (k ∧ (~ i ∨ j)) ∨ ((i ∨ k) ∧ j) ∨ ((~ i) ∧ k) ∨ (i ∧ j)
  if' i then j else k end =  ((~ i) ∧ k) ∨ (i ∧ j)

  encode : {i j i' j' : I} {c : cpd A A i j} {c' : cpd A A i' j'} (p : PathP (λ k → cpd A A (if k then i' else i end) (if k then j' else j end)) c c') → Cover c c'
  encode {i} {j} {i'} {j'} {c} p = transport (λ k → Cover c (p k)) (reflCode i j c)

  decode : {i j i' j' : I} {c : cpd A A i j} {c' : cpd A A i' j'} → Cover c c' → PathP (λ k → cpd A A (if k then i' else i end) (if k then j' else j end)) c c'
  decode {c = inl x} {c' = inl y} p = λ k → inl (p k)
  decode {c = inr x} {c' = inr y} p = λ k → inr (p k)


  decodeEncode : {i j i' j' : I} {c : cpd A A i j} {c' : cpd A A i' j'} (p : PathP (λ k → cpd A A (if k then i' else i end) (if k then j' else j end)) c c')
                 → decode {c = c} {c' = c'} (encode p) ≡ p
  -- decodeEncode {c = inl x} = J (λ c' p → decode (encode p) ≡ p) (cong (cong inl) (transportRefl refl))
  -- decodeEncode {c = inr x} = J (λ c' p → decode (encode p) ≡ p) (cong (cong inr) (transportRefl refl))
  decodeEncode {i} {j} {i'} {j'} {c = inl x} {c'} p =
    -- JDep (λ y p z q → decode (encode q) ≡ q) {!!} {!!} {!!}
    transport
    (λ k → decode {c = inl x} {c' = p k} (encode {c = inl x} {c' = p k} (λ k' → p (k ∧ k'))) ≡ λ k' → p (k ∧ k'))
    λ k k' → {!transp (λ k'' → cpd A A (if (k' ∧ k'') then i else i end) (if (k' ∧ k'') then j else j end)) (~ k') (inl x)!}
    -- k = 0 then A i j
    -- k = 1 then A i j
    -- λ k k' → inl {!transp (λ k → A (if (k ∧ k') then (if i0 then i' else i end) else i end) (if (k ∧ k') then (if i0 then j' else j end) else j end)) i0 x!}
    -- (λ k k' → inl (comp
    --                 (λ k →
    --                    A if k ∧ k' then if i0 then i' else i end else i end
    --                    if k ∧ k' then if i0 then j' else j end else j end)
    --                 (λ where
    --                   l (k' = i0) → {!!}) x))
    -- (λ k → {!transport-filler!})
  decodeEncode {c = inr x} p =
    transport
    (λ k → decode {c = inr x} {c' = p k} (encode {c = inr x} {c' = p k} (λ k' → p (k ∧ k'))) ≡ λ k' → p (k ∧ k'))
    {!!}
  -- decodeEncode {c = inr x} = JDep {!!} (λ c' p → PathP {!!} (decode (encode p)) p) (cong (cong inr) (transportRefl refl))

  sqFillCoproduct : sqFill (cpd A A)
  sqFillCoproduct {inl lu} {inl ld} l {inl ru} {inl rd} r u d i j =
    (comp (λ k → cpd A A i j)
      (λ where
        k (i = i0) → decodeEncode l k j
        k (i = i1) → decodeEncode r k j
        k (j = i0) → decodeEncode u k i
        k (j = i1) → decodeEncode d k i)
      (inl {A} {A} (sqFillA (encode l) (encode r) (encode u) (encode d) i j)))
      -- {! inl {A} {A} (sqFillA (encode l) (encode r) (encode u) (encode d) i j) !}
  sqFillCoproduct {inr lu} {inr ld} l {inr ru} {inr rd} r u d i j = {!!}
    -- (hcomp (λ where
    --     k (i = i0) → decodeEncode l k j
    --     k (i = i1) → decodeEncode r k j
    --     k (j = i0) → decodeEncode u k i
    --     k (j = i1) → decodeEncode d k i)
    --   (inr {A} {A} (sqFillA (encode l) (encode r) (encode u) (encode d) i j)))
  sqFillCoproduct {inl x} {inr y} l _ _ _ = ⊥-elim (inl≠inr x y l)
  sqFillCoproduct {inr x} {inl y} l _ _ _ = ⊥-elim (inl≠inr y x (λ k → l (~ k)))
  sqFillCoproduct {inl x} {_} _ {inr y} _ u _ = ⊥-elim (inl≠inr x y u)
  sqFillCoproduct {inr x} {_} _ {inl y} _ u _ = ⊥-elim (inl≠inr y x (λ k → u (~ k)))
  sqFillCoproduct {_} {inl x} _ {_} {inr y} _ _ d = ⊥-elim (inl≠inr x y d)
  sqFillCoproduct {_} {inr x} _ {_} {inl y} _ _ d = ⊥-elim (inl≠inr y x (λ k → d (~ k)))
  -- sqFillCoproduct {_} {_} _ {inl x} {inr y} r _ _ = ⊥-elim (inl≠inr x y r)
  -- sqFillCoproduct {_} {_} _ {inr x} {inl y} r _ _ = ⊥-elim (inl≠inr y x (λ k → r (~ k)))

  sqFillPath : {a : (i j : I) → A i j} → sqFill (λ i j → a i j ≡ a i j)
  sqFillPath {a} {lu} {ld} l {ru} {rd} r u d i j =
    comp (λ k → a (i ∧ k) (j ∧ k) ≡ a (i ∧ k) (j ∧ k))
         (λ k → λ { (i = i0) → {!sqFillA (λ i → lu i)!}
                  ; (i = i1) → {!!}
                  ; (j = i0) → {!!}
                  ; (j = i1) → {!!}}) lu

-- third version
module ISqFill where
  SqFill : {ℓ : Level} → (A : I → I → Type ℓ) → Type ℓ
  SqFill A =
    {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
    {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
    (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
    → SquareP A a₀₋ a₁₋ a₋₀ a₋₁

  ISqFill : (Θ : I → I → Type) → (A : (i j : I) → Θ i j → Type) → Type
  ISqFill Θ A = SqFill (λ i j → (θ : Θ i j) → A i j θ)

  -- private variable
  postulate
    Θ : I → I → Type
    A : (i j : I) → Θ i j → Type
    B : (i j : I) → (θ : Θ i j) → (x : A i j θ) → Type

  postulate
    ISqFillB : ISqFill (λ i j → Σ[ θ ∈ Θ i j ] A i j θ) λ{i j (θ , a) → B i j θ a}

  ISqFillPi : ISqFill Θ (λ i j θ → (a : A i j θ) → B i j θ a)
  ISqFillPi {a₀₀ = f00} {f01} l {f10} {f11} r u d i j θ a =
    ISqFillB (λ j' → uncurry (l j')) (λ j' → uncurry (r j')) (λ i' → uncurry (u i')) (λ i' → uncurry (d i')) i j (θ , a)

  postulate
    ISqFillA : ISqFill Θ A
    ISqFillB' : (a : ∀ (i j : I) (θ : Θ i j) → A i j θ) → ISqFill Θ (λ i j θ → B i j θ (a i j θ))

  ISqFillSigma : ISqFill Θ (λ i j θ → Σ[ a ∈ A i j θ ] B i j θ a)
  ISqFillSigma {a₀₀ = f00} {f01} l {f10} {f11} r u d i j θ .fst = ISqFillA (λ j' θ → l j' θ .fst) (λ j' θ → r j' θ .fst) (λ i' θ → u i' θ .fst) (λ j' θ → d j' θ .fst) i j θ
  ISqFillSigma {a₀₀ = f00} {f01} l {f10} {f11} r u d i j θ .snd =
    ISqFillB' (λ i j θ → ISqFillSigma l r u d i j θ .fst)
      (λ j' θ → l j' θ .snd) ((λ j' θ → r j' θ .snd)) ((λ i' θ → u i' θ .snd)) ((λ i' θ → d i' θ .snd))
      i j θ
    --ISqFillB {A = λ i j θ → B i j θ (ISqFillSigma l r u d i j θ .fst)} (λ j' θ,a → {!!}) ((λ j' (θ , a) → r j' θ .snd)) ((λ i' (θ , a) → u i' θ .snd)) ((λ i' (θ , a) → d i' θ .snd)) i j {!!}

  -- ISqFillB (λ j' → uncurry (l j')) (λ j' → uncurry (r j')) (λ i' → uncurry (u i')) (λ i' → uncurry (d i')) i j (θ , a)
  data Bool {ℓ} : Type ℓ where
    true : Bool
    false : Bool

  -- data ⊤ : Type where
  --   tt : ⊤

  -- ISqFillBool : ISqFill Θ (λ _ _ _ → ⊤)
  -- ISqFillBool {b00} l r u d i j θ = {!tt!}
  --   where
  --     rjθ≡tt : ∀ {θ'} → r j θ' ≡ tt
  --     rjθ≡tt k = {!transp!}
