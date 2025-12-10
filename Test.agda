{-# OPTIONS --cubical=no-glue --guardedness #-}
{-# OPTIONS -v cubical.prim.uip:70 #-}

open import Agda.Primitive using () renaming (Set to Type)
open import Agda.Primitive.Cubical public
  renaming ( primIMin       to _∧_  -- I → I → I
           ; primIMax       to _∨_  -- I → I → I
           ; primINeg       to ~_   -- I → I
           ; isOneEmpty     to empty
           ; primComp       to comp
           ; primHComp      to hcomp
           ; primTransp     to transp
           ; itIsOne        to 1=1 )
open import Agda.Primitive.Cubical public
open import Agda.Builtin.Cubical.Path public

open import SqFill
-- open import SqPFill

-- primitive primIMin : I → I → I
primitive
  -- prim^sqFill : (A : Type)
  --   {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
  --   {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
  --   (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
  --   → PathP (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋
  prim^sqFill : (A : Type) → SqFill A
    -- {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
    -- {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
    -- (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
    -- → PathP (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋
-- postulate
--   pos^sqFill : (A : Type)
--     {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
--     {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
--     (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
--     → PathP (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋
  -- prim^sqFill : Type

sqFill = prim^sqFill

-- module hello (A B : Type) where
--   p : SqFill (A → B)
--   p = prim^sqFill (A → B)

--   postulate SqFillB : SqFill B

--   q = SqFill.SqFillPi.SqFillPiAB A (λ ^ → B) (λ _ → prim_sqFill B)

--   check : p ≡ q
--   check k = {!!}
--   -- p' : p ≡ SqFill.SqFillPi.SqFillPiAB A (λ _ → B) λ _ → prim_sqFill B
--   -- p' k l r u d i j a = {!p l r u d i j a!}
--   -- p' k = {!!}

module hello-dep (A : Type) (B : A → Type)
  (SqFillB : (a : A) → SqFill (B a))
  where
  p : SqFill ((a : A) → B a)
  -- p = λ l r u d i j → prim^sqFill ((a : A) → B a) l r u d i j
  p = prim^sqFill ((a : A) → B a)

  sqFillB : (a : A) → SqFill (B a)
  sqFillB a = prim^sqFill (B a)

  q : (a₀₀ a₀₁ : (a : A) → B a) (a₀₋ : a₀₀ ≡ a₀₁)
    (a₁₀ a₁₁ : (a : A) → B a) (a₁₋ : a₁₀ ≡ a₁₁)
    (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
    → PathP (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋
  -- q (lu) (ld) = SqFillPiAB A (λ a → B a) (λ a (lu) (ld) → prim^sqFill (B a) (lu) (ld)) (lu) (ld)
  q = SqFill.SqFillPi.SqFillPiAB A (λ a → B a) (λ a → prim^sqFill (B a))
  -- q = SqFill.SqFillPi.SqFillPiAB A (λ a → B a) sqFillB

  -- postulate
  --   lu ld ru rd : (a : A) → B a
  --   l : lu ≡ ld
  --   r : ru ≡ rd
  --   u : lu ≡ ru
  --   d : ld ≡ rd
  --   i j : I
  --   a : A
  -- check : _≡_ {A = SqFill ((a : A) → B a)} (λ {lu} {ld} → p {lu} {ld}) (λ {lu} {ld} → q {lu} {ld})
  check : p ≡ q
  -- check = {!!}
  -- check : (λ {lu} {ld} → p {lu} {ld}) ≡ q
  -- check : (λ {lu} {ld} → q {lu} {ld}) ≡ p
    -- {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
    -- {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
    -- (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
    -- → PathP (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋
  -- check k {lu} {ld} l {ru} {rd} r u d i j a = {!q!}
  -- check = λ i a₀₋ a₁₋ a₋₀ a₋₁ i₁ i₂ a → {!!}
  -- check k l r u d i j a = {!!}
  -- check = λ i₁ a₀₀ a₀₁ a₀₋ a₁₀ a₁₁ a₁₋ a₋₀ a₋₁ i₂ i₃ a₁ → {!!}
  check k = {!!}
  -- check k = λ a₀₀ a₀₁ a₀₋ a₁₀ a₁₁ a₁₋ a₋₀ a₋₁ → {!prim^sqFill!}
  -- check = {!!}
  -- check = λ i a₀₋ a₁₋ a₋₀ a₋₁ i₁ i₂ a → {!!}
  -- p' : p ≡ SqFill.SqFillPi.SqFillPiAB A (λ _ → B) λ _ → prim^sqFill B
  -- p' k l r u d i j a = {!p l r u d i j a!}
  -- p' k = {!!}

-- module hello-dep' (A : Type) (B : A → Type) (SqFillB : (a : A) → SqFill (B a)) where
--   data Bool : Type where
--     true : Bool
--     false : Bool

--   p : SqFill Bool
--   p = prim^sqFill Bool

--   q = SqFill.SqFillPi.SqFillPiAB A (λ a → B a) (λ a → prim^sqFill (B a))

--   check : p ≡ q
--   check = {! !}
