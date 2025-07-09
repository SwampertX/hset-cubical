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

  test : A
  test = transport refl a

  Test : Type
  Test = transport refl A

  issetPiAB : isSet ((x : A) → B x)
  issetPiAB f g p q i j x = issetB x (f x) (g x) (λ i → p i x) (λ i → q i x) i j

  issetSigmaAB : isSet (Σ[ a ∈ A ] B a)
  issetSigmaAB x y p q i j .fst = issetA (x .fst) (y .fst) (λ i → p i .fst) (λ i → q i .fst) i j
  issetSigmaAB x y p q i j .snd =
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
  -- if k then i else j end = ((~ k) ∧ j) ∨ (k ∧ i)
  -- if k then i else j end = (j ∨ ~ k) ∧ (i ∨ k)
  if i then j else k end = (k ∧ ~ i) ∨ ((i ∨ k) ∧ j)

  {-# INLINE if_then_else_end #-}

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
      spread i j i' j' k = sqa (if k then i' else i end) (if k then j' else j end)

      -- spreadRegular : (i j : I) → spread i j i j ≡ refl
      -- spreadRegular i j = refl

      lub : B (fst lu)
      lub = snd lu
      lub' : B (sqa i j)
      lub' = transport (λ k → B (spread i0 i0 i j k)) lub
      LemmaLU : PathP (λ k → B (sqa (if k then i else i0 end) (if k then j else i0 end))) lub lub'
      LemmaLU = transport-filler _ lub

      ldb : B (fst ld)
      ldb = snd ld
      ldb' : B (sqa i j)
      ldb' = transport (λ k → B (spread i0 i1 i j k)) ldb
      LemmaLD : PathP (λ k → B (sqa (if k then i else i0 end) (if k then j else i1 end))) ldb ldb'
      LemmaLD = transport-filler _ ldb

      lb : PathP (λ j → B (sqa i0 j)) lub ldb
      lb = cong snd l

      rub : B (fst ru)
      rub = snd ru
      rub' : B (sqa i j)
      rub' = transport (λ k → B (spread i1 i0 i j k)) rub
      LemmaRU : PathP (λ k → B (sqa (if k then i else i1 end) (if k then j else i0 end))) rub rub'
      LemmaRU = transport-filler _ rub

      rdb : B (fst rd)
      rdb = snd rd
      rdb' : B (sqa i j)
      rdb' = transport (λ k → B (spread i1 i1 i j k)) rdb
      LemmaRD : PathP (λ k → B (sqa (if k then i else i1 end) (if k then j else i1 end))) rdb rdb'
      LemmaRD = transport-filler _ rdb

      rb : PathP (λ j → B (sqa i1 j)) rub rdb
      rb = cong snd r

      ub : PathP (λ i → B (sqa i i0)) lub rub
      ub = cong snd u

      db : PathP (λ i → B (sqa i i1)) ldb rdb
      db = cong snd d

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
      lb' : lub' ≡ ldb'
      lb' i' = comp (λ k → B (sqa (if k then i else i0 end) (if k then j else i' end))) (λ{
          j' (i' = i0) → LemmaLU j' ;
          j' (i' = i1) → LemmaLD j'
        }) (lb i')

      rb' : rub' ≡ rdb'
      rb' i' = comp (λ k → B (sqa (if k then i else i1 end) (if k then j else i' end))) (λ{
          j' (i' = i0) → LemmaRU j' ;
          j' (i' = i1) → LemmaRD j'
        }) (rb i')

      ub' : lub' ≡ rub'
      ub' i' = comp (λ k → B (sqa (if k then i else i' end) (if k then j else i0 end))) (λ{
          j' (i' = i0) → LemmaLU j' ;
          j' (i' = i1) → LemmaRU j'
        }) (ub i')

      db' : ldb' ≡ rdb'
      db' i' = comp (λ k → B (sqa (if k then i else i' end) (if k then j else i1 end))) (λ{
          j' (i' = i0) → LemmaLD j' ;
          j' (i' = i1) → LemmaRD j'
        }) (db i')

  --   -- either we fill the general square at B (αij) for any i j (we need to transport wiggle each side up to i,j)
  --   sqfillB (sqfillSigmaAB l r u d i j .proj₁) {!fromPathP (cong snd l)!} {!!} {!!} {!!} i {!!}
  --   -- or first wiggle our square to the comfortable transatlantic position and fill in the sides.
  --   -- toPathP (toPathP {!!}) i

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

  -- open import Data.Unit

  -- issetTop : isSet ⊤
  -- issetTop tt tt refl refl i j = tt

  -- open import Data.Empty

  -- issetBot : isSet ⊥
  -- issetBot ()

  -- open import Data.Nat

  -- znots : (n : ℕ) → zero ≡ suc n → ⊥
  -- znots n p = subst c p tt
  --   where
  --     c : ℕ → _
  --     c zero = ⊤
  --     c (suc n) = ⊥

  -- snotz : (n : ℕ) → suc n ≡ zero → ⊥
  -- snotz n p = subst c p tt
  --   where
  --     c : ℕ → _
  --     c zero = ⊥
  --     c (suc n) = ⊤

  -- codeℕ : (x y : ℕ) → Type
  -- codeℕ zero zero = ⊤
  -- codeℕ zero (suc _) = ⊥
  -- codeℕ (suc _) zero = ⊥
  -- codeℕ (suc n) (suc m) = codeℕ n m

  -- encodeℕ : (x y : ℕ) → x ≡ y → codeℕ x y
  -- encodeℕ x y p = transport (λ i → codeℕ x (p i)) (r x)
  --   where
  --     r : (x : ℕ) → codeℕ x x
  --     r zero = tt
  --     r (suc x) = r x

  -- decodeℕ : (x y : ℕ) → codeℕ x y → x ≡ y
  -- decodeℕ zero zero tt = refl
  -- decodeℕ (suc x) (suc y) c = cong suc (decodeℕ x y c)


  -- isSetAA→isSetA : {A : Type} → isSet (A × A) → isSet A
  -- isSetAA→isSetA issetAA a b p q i j = issetAA (a , a) (b , b) (λ i → (p i , p i)) (λ i → (q i , q i)) i j .proj₁

  -- isPropisProp : (A : Type) → isProp (isProp A)
  -- isPropisProp A f g i a b j = {!!}

  -- isPropUIP : (A : Type) → isProp (isSet A)
  -- isPropUIP A f g i a b p q j = {!!}

  -- issetPiAB→issetB : {A : Type} {B : A → Type} → isSet ((x : A) → B x) → (x : A) → isSet (B x)
  -- issetPiAB→issetB h x b1 b2 p q = {!isSetB!}

  SquareP' : (ℓ : Level)
    (A : I → I → Type ℓ)
    {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP {ℓ = ℓ} (λ j → A i0 j) a₀₀ a₀₁)
    {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
    (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
    → Type ℓ
  SquareP' ℓ A a₀₋ a₁₋ a₋₀ a₋₁ = PathP (λ i → PathP (λ j → A i j) (a₋₀ i) (a₋₁ i)) a₀₋ a₁₋

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

  data ⊤ : Type where
    tt : ⊤

  -- ISqFillBool : ISqFill Θ (λ _ _ _ → ⊤)
  -- ISqFillBool {b00} l r u d i j θ = {!tt!}
  --   where
  --     rjθ≡tt : ∀ {θ'} → r j θ' ≡ tt
  --     rjθ≡tt k = {!transp!}

  _ = {!Iso!}
