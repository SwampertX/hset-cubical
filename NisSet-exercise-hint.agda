{-# OPTIONS --without-K #-}
-- We do not assume that "any proof of a≡a is reflexivity", i.e. Streicher's Axiom K.
-- In fact, we will prove that natural numbers satisfy K.

open import Agda.Primitive renaming (Set to Type)
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

_∘_ : {A B C : Type} → (B → C) → (A → B) → A → C
f ∘ g = λ a → f (g a)

postulate fixme : ∀ {ℓ} {A : Type ℓ} → A

-- standard exercise: prove that equality is symmetric, transitive, and congruent.
cong : {A B : Type} {a a' : A} (f : A → B) → a ≡ a' → f a ≡ f a'
cong = fixme

sym : {A : Type} {a b : A} → a ≡ b → b ≡ a
sym = fixme

trans : {A : Type} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans = fixme

transport : {A : Type} {a b : A} → (P : A → Type) → a ≡ b → P a → P b
transport = fixme

-- the empty type has no constructor.
data ⊥ : Type where

¬_ : Type → Type
¬ A = A → ⊥

⊥-elim : ∀ {ℓ} {A : Type ℓ} → ⊥ → A
⊥-elim = fixme

-- We say a Type is a set if any two proofs of an equality must be equal.
isSet : Type → Type
isSet A = (a b : A) → (p q : a ≡ b) → p ≡ q

pred : Nat → Nat
pred = fixme

data _⊎_ (A B : Type) : Type where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

-- this is optional, but might inspire you for the next exercise
open import Agda.Builtin.Bool

natEqb : (n m : Nat) → Bool
natEqb = fixme

-- We say a type has decidable equality if there is a function that
-- takes two elements, and returns either a proof that they are equal,
-- or disprove that they are equal.
eqDec : (A : Type) → Type
eqDec A = (a b : A) → (a ≡ b) ⊎ (¬(a ≡ b))

-- show that natural numbers have decidable equality.
-- first, you need to prove the no-confusion principle: zero is not equal to suc.
-- hint: define a function Nat → Type that is equals ⊥ when the input is not zero, and use transport.
zero≠suc : ∀ {m} → (zero ≡ suc m) → ⊥
zero≠suc p = fixme
  where
    isZero : Nat → Type
    isZero = fixme

-- now show decidable equality of natural numbers.
-- you can use with-abstraction https://agda.readthedocs.io/en/latest/language/with-abstraction.html#with-abstraction
-- to help you.
-- hint: needs recursion.
eqDecNat : (n m : Nat) → (n ≡ m) ⊎ (¬(n ≡ m))
eqDecNat = fixme

-- we are ready to show that natural numbers is a set.

-- composing a≡b with b≡a is always refl.
cancel : {A : Type} {a b : A} (p : a ≡ b) → refl ≡ trans (sym p) p
cancel = fixme

-- the key is noticing that any proof (p : a ≡ b) is equal to (eqDec a a) ⁻¹ ∙ (eqDec a b)
-- i.e. a normal form. then p = q by transitivity.

-- we state the normal form in terms of eqDeqA, a, b, p.
normalForm : {A : Type} (eqDecA : eqDec A) (a b : A) (p : a ≡ b) → Type
normalForm eqDecA a b p with eqDecA a a | eqDecA a b
... | inl a≡a  | inl a≡b  = p ≡ trans (sym a≡a) a≡b
... | inl a≡a  | inr ¬a≡b = ⊥-elim (¬a≡b p)
... | inr ¬a≡a | _        = ⊥-elim (¬a≡a refl)

-- we show the normal form by path induction.
theNormalForm : {A : Type} (eqDecA : eqDec A) (a b : A) (p : a ≡ b) → normalForm eqDecA a b p
theNormalForm eqDecA a .a refl with eqDecA a a
... | inl a≡a  = fixme
... | inr ¬a≡a = fixme

eqDec→isSet : (A : Type) → (eqDecA : (a b : A) → (a ≡ b) ⊎ (¬(a ≡ b))) → isSet A
eqDec→isSet A eqDecA a b p q with eqDecA a a | eqDecA a b | theNormalForm eqDecA a b p | theNormalForm eqDecA a b q
... | inl a≡a | inl a≡b | p≡nf | q≡nf = fixme
... | inr ¬a≡a | _ | _ | _ = fixme
... | _ | inr ¬a≡b | _ | _ = fixme

-- now specialize the result to Nats.
natIsSet : isSet Nat
natIsSet = fixme

-- now show that UIP <-> K. Only one direction is needed, but the other is trivial.
hasK : Type → Type
hasK A = (a : A) → (p : a ≡ a) → p ≡ refl

isSet→hasK : {A : Type} → (isSet A → hasK A)
isSet→hasK = fixme

hasK→isSet : {A : Type} → (hasK A → isSet A)
hasK→isSet = fixme

-- now we should have K for Nat.
natHasK : hasK Nat
natHasK = fixme
