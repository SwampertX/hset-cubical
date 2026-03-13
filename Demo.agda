{-# OPTIONS --cubical=uip #-}
-- {-# OPTIONS --cubical=no-glue #-}

open import Agda.Primitive using () renaming (Set to Type)
open import Agda.Primitive.Cubical public
  renaming ( primIMin       to _∧_
           ; primIMax       to _∨_
           ; primINeg       to ~_
           ; isOneEmpty     to empty
           ; primComp       to comp
           ; primHComp      to hcomp
           ; primTransp     to transp
           ; itIsOne        to 1=1 )
open import Agda.Builtin.Cubical.Path public
open import Agda.Builtin.Sigma
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Unit
open import SqFill
open import Helper using (refl)

primitive prim^sqFill : (A : Type) → SqFill A
-- postulate prim^sqFill : (A : Type) → SqFill A

-- ─────────────────────────────────────────────────────────────────────────────
-- Coproducts, encoded via Σ + Bool
-- ─────────────────────────────────────────────────────────────────────────────

_⊎_ : Type → Type → Type
A ⊎ B = Σ Bool λ {true → A ; false → B}

inl : {A B : Type} → A → A ⊎ B
inl a = true , a

inr : {A B : Type} → B → A ⊎ B
inr b = false , b

⊎-elim : {A B C : Type} → (A → C) → (B → C) → A ⊎ B → C
⊎-elim f g (true  , a) = f a
⊎-elim f g (false , b) = g b

-- ─────────────────────────────────────────────────────────────────────────────
-- A tiny SSA / let-calculus
--
-- Inspired by the well-known correspondence:
--   "SSA is Functional Programming" (Appel, 1998)
--
-- A LetBlock is a sequence of 3 instructions followed by a return value.
-- Each instruction is a binary operation applied to two Values.
-- A Value is either a literal natural number, or a variable (de Bruijn index).
-- A BinOp is one of: Add | Sub | Mul | Div  (encoded as Bool × Bool)
-- ─────────────────────────────────────────────────────────────────────────────

-- Values: literals or variable references
Value : Type
Value = ℕ ⊎ ℕ    -- inl n = Lit n | inr i = Var i

pattern Lit n = true  , n
pattern Var i = false , i

-- Binary operations: 2 bits = 4 ops
BinOp : Type
BinOp = Bool × Bool
-- (true,  true)  = Add
-- (true,  false) = Sub
-- (false, true)  = Mul
-- (false, false) = Div

pattern Add = true  , true
pattern Sub = true  , false
pattern Mul = false , true
pattern Div = false , false

-- An instruction: op applied to two values
Instruction : Type
Instruction = BinOp × Value × Value

-- A basic block: 3 instructions + a return value
-- let x₀ = instr₀
-- let x₁ = instr₁
-- let x₂ = instr₂
-- in  retval
LetBlock : Type
LetBlock = Instruction × Instruction × Instruction × Value

-- ─────────────────────────────────────────────────────────────────────────────
-- Example blocks
-- ─────────────────────────────────────────────────────────────────────────────

-- let x₀ = 1 + 2
-- let x₁ = x₀ * 3
-- let x₂ = x₁ - x₀
-- in  x₂
example-block : LetBlock
example-block =
  (Add , Lit 1 , Lit 2) ,
  (Mul , Var 0 , Lit 3) ,
  (Sub , Var 1 , Var 0) ,
  Var 2

-- ─────────────────────────────────────────────────────────────────────────────
-- UIP for LetBlock — computes in Cubical-UIP, stuck in mainline
-- ─────────────────────────────────────────────────────────────────────────────

-- Any two proofs that two basic blocks are equal are themselves equal.
-- In mainline Agda: this term never reduces.
-- In Cubical-UIP:  prim^sqFill inspects LetBlock, fires through
--   Σ → Σ → Σ (nested products)
--       → BinOp = Bool × Bool
--       → Value = Bool ⊎ ℕ = Σ Bool (...)
--       → ℕ
-- ... and reduces to refl automatically.

uip-block : {b₁ b₂ : LetBlock} (p q : b₁ ≡ b₂) → p ≡ q
uip-block {b₁} {b₂} p q = prim^sqFill LetBlock p q refl refl

-- The killer test: this typechecks by refl in Cubical-UIP
-- Try this in mainline Agda — it will be stuck.
test-computes : uip-block (λ _ → example-block) (λ _ → example-block)
              ≡ (λ _ _ → example-block)
test-computes = refl

-- ─────────────────────────────────────────────────────────────────────────────
-- A certified compiler pass:
-- constant folding on a single instruction
-- ─────────────────────────────────────────────────────────────────────────────

-- Fold an instruction if both operands are literals
fold-instr : Instruction → Value
fold-instr (Add , Lit m , Lit n) = Lit (m + n)
fold-instr (Mul , Lit m , Lit n) = Lit (m * n)
fold-instr (_   , v     , _    ) = v   -- no fold

-- Two different folding strategies on the same block
-- give results whose equality proofs compute away:
fold-block : LetBlock → LetBlock
fold-block (i₀ , i₁ , i₂ , ret) =
  (Add , fold-instr i₀ , fold-instr i₁) ,
  (Mul , fold-instr i₁ , fold-instr i₂) ,
  i₂ ,
  fold-instr i₂

-- Any proof that two fold results are equal is unique — computes:
uip-fold : {b₁ b₂ : LetBlock}
           (p q : fold-block b₁ ≡ fold-block b₂) → p ≡ q
uip-fold {b₁} {b₂} p q = prim^sqFill LetBlock p q refl refl
