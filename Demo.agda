{-# OPTIONS --cubical=uip #-}

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
open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Product
open import Agda.Builtin.Coproduct
open import SqFill
open import SqFillDef
open import Helper using (refl)

primitive prim^sqFill : {l : Level} (A : Type l) → SqFill A

-- ─────────────────────────────────────────────────────────────────────────────
-- Coproducts via Σ + Bool  (prim^sqFill handles these via the Sigma/Bool rules)
-- ─────────────────────────────────────────────────────────────────────────────

-- _⊎_ : Type → Type → Type
-- A ⊎ B = Σ Bool λ {true → A ; false → B}

-- inl : {A B : Type} → A → A ⊎ B
-- inl a = true , a

-- inr : {A B : Type} → B → A ⊎ B
-- inr b = false , b

⊎-elim : {A B C : Type} → (A → C) → (B → C) → A ⊎ B → C
⊎-elim f g (inl a) = f a
⊎-elim f g (inr b) = g b

-- ─────────────────────────────────────────────────────────────────────────────
-- A register-transfer language (RTL)
--
-- Inspired by "SSA is Functional Programming" (Appel 1998).
--
-- Values are:
--   Lit n  — a known compile-time literal
--   Var i  — de Bruijn reference to the result of instruction i
--   Unk    — statically unknown (function argument, external input, etc.)
--
-- The Unk constructor is modelled by Maybe: nothing = unknown.
-- This is new relative to the original LetBlock demo, which had no unknowns.
--
-- A Program is a variable-length List of instructions, more realistic than
-- a fixed-3-instruction block.
-- ─────────────────────────────────────────────────────────────────────────────

BinOp : Type
BinOp = Bool × Bool

pattern Add = true  , true
pattern Sub = true  , false
pattern Mul = false , true
pattern Div = false , false

Value : Type
Value = Maybe (ℕ ⊎ ℕ)

pattern Lit n = just (inl n)
pattern Var i = just (inr i)
pattern Unk   = nothing

Instruction : Type
Instruction = BinOp × Value × Value

Program : Type
Program = List Instruction × Value

-- ─────────────────────────────────────────────────────────────────────────────
-- Example programs
-- ─────────────────────────────────────────────────────────────────────────────

-- r₀ := 1 + 2   (= 3)
-- r₁ := r₀ * 3  (= 9)
-- r₂ := r₁ - r₀ (= 6)
-- return r₂
prog-arith : Program
prog-arith =
  (Add , Lit 1 , Lit 2) ∷
  (Mul , Var 0 , Lit 3) ∷
  (Sub , Var 1 , Var 0) ∷
  [] , Var 2

-- r₀ := ? + 1    (? = statically unknown input, e.g. a function argument)
-- r₁ := r₀ * r₀
-- return r₁       (computes (input+1)²)
prog-square-succ : Program
prog-square-succ =
  (Add , Unk  , Lit 1) ∷
  (Mul , Var 0 , Var 0) ∷
  [] , Var 1

-- trivial: just return a literal
prog-const : Program
prog-const = [] , Lit 42

-- ─────────────────────────────────────────────────────────────────────────────
-- UIP for Program — computes in Cubical-UIP, stuck in mainline Agda
--
-- prim^sqFill traverses the full type tower:
--   Program     = List Instruction × Value   ← List is new
--   Instruction = BinOp × Value × Value
--   Value       = Maybe (ℕ ⊎ ℕ)              ← Maybe is new
--   BinOp       = Bool × Bool
--   ℕ ⊎ ℕ       = Σ Bool (const ℕ)
-- All constructors are supported → reduces to refl automatically.
-- ─────────────────────────────────────────────────────────────────────────────

uip-prog : {p q : Program} (α β : p ≡ q) → α ≡ β
uip-prog α β = prim^sqFill Program α β refl refl

-- These typecheck by refl: uip collapses to the identity path
test-arith : uip-prog (λ _ → prog-arith) (λ _ → prog-arith) ≡ (λ _ _ → prog-arith)
test-arith = refl

test-square-succ : uip-prog (λ _ → prog-square-succ) (λ _ → prog-square-succ)
                 ≡ (λ _ _ → prog-square-succ)
test-square-succ = refl

test-const : uip-prog (λ _ → prog-const) (λ _ → prog-const)
           ≡ (λ _ _ → prog-const)
test-const = refl

-- ─────────────────────────────────────────────────────────────────────────────
-- Constant folding — a certified compiler pass
--
-- fold-instr : if both operands are known literals, returns just (Lit result).
--              otherwise returns nothing (cannot fold).
-- fold-prog : runs fold-instr over the instruction list, producing a
--             "known-value map" — a List (Maybe Value) — one entry per step.
--
-- The output type List (Maybe Value) nests both new features and still
-- admits UIP.
-- ─────────────────────────────────────────────────────────────────────────────

eval : BinOp → ℕ → ℕ → ℕ
eval Add m n = m + n
eval Mul m n = m * n
eval Sub m n = m - n
eval Div m _ = m       -- division uninterpreted (no builtin div)

fold-instr : Instruction → Maybe Value
fold-instr (op , Lit m , Lit n) = just (Lit (eval op m n))
fold-instr _                    = nothing

fold-prog : Program → List (Maybe Value)
fold-prog ([]       , _) = []
fold-prog (i ∷ rest , r) = fold-instr i ∷ fold-prog (rest , r)

uip-fold : {xs ys : List (Maybe Value)} (α β : xs ≡ ys) → α ≡ β
uip-fold α β = prim^sqFill (List (Maybe Value)) α β refl refl

-- fold-prog prog-arith:
--   (Add, Lit 1, Lit 2) → just (Lit 3)
--   (Mul, Var 0, Lit 3) → nothing      (Var 0 is not a literal)
--   (Sub, Var 1, Var 0) → nothing
test-fold-arith : fold-prog prog-arith ≡ just (Lit 3) ∷ nothing ∷ nothing ∷ []
test-fold-arith = refl

test-fold-uip : uip-fold (λ _ → fold-prog prog-arith) (λ _ → fold-prog prog-arith)
              ≡ (λ _ _ → fold-prog prog-arith)
test-fold-uip = refl

_ = {!uip-fold (λ _ → fold-prog prog-arith) (λ _ → fold-prog prog-arith)!}

-- ─────────────────────────────────────────────────────────────────────────────
-- Live variable analysis
--
-- Which register indices are referenced by the return value?
-- Returns a List ℕ — another natural analysis output type.
-- ─────────────────────────────────────────────────────────────────────────────

live-ret : Value → List ℕ
live-ret (Var i) = i ∷ []
live-ret _       = []

uip-live : {xs ys : List ℕ} (α β : xs ≡ ys) → α ≡ β
uip-live α β = prim^sqFill (List ℕ) α β refl refl

-- prog-arith returns Var 2, so only register 2 is live at exit
test-live : live-ret (Var 2) ≡ 2 ∷ []
test-live = refl

test-live-uip : uip-live (λ _ → live-ret (Var 2)) (λ _ → live-ret (Var 2))
              ≡ (λ _ _ → live-ret (Var 2))
test-live-uip = refl
