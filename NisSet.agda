{-# OPTIONS --without-K #-}
-- We do not assume that "any proof of a≡a is reflexivity", i.e. Streicher's Axiom K.
-- In fact, we will prove that natural numbers satisfy K.

open import Agda.Primitive renaming (Set to Type)
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

_∘_ : {A B C : Type} → (B → C) → (A → B) → A → C
f ∘ g = λ a → f (g a)

-- standard exercise: prove that equality is symmetric, transitive, and congruent.
cong : {A B : Type} {a a' : A} (f : A → B) → a ≡ a' → f a ≡ f a'
cong f refl = refl

sym : {A : Type} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {A : Type} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl q = q

transport : {A : Type} {a b : A} → (P : A → Type) → a ≡ b → P a → P b
transport P refl pa = pa

-- the empty type has no constructor.
data ⊥ : Type where

¬_ : Type → Type
¬ A = A → ⊥

⊥-elim : ∀ {ℓ} {A : Type ℓ} → ⊥ → A
⊥-elim ()

-- We say a Type is a set if any two proofs of an equality must be equal.
isSet : Type → Type
isSet A = (a b : A) → (p q : a ≡ b) → p ≡ q

pred : Nat → Nat
pred zero = zero
pred (suc a) = a

data _⊎_ (A B : Type) : Type where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

-- open import Agda.Builtin.Bool

-- natEqb : (n m : Nat) → Bool
-- natEqb zero zero = true
-- natEqb zero (suc _) = false
-- natEqb (suc n) (suc m) = natEqb n m
-- natEqb (suc _) zero = false

-- We say a type has decidable equality if there is a function that
-- takes two elements, and returns either a proof that they are equal,
-- or disprove that they are equal.
eqDec : (A : Type) → Type
eqDec A = (a b : A) → (a ≡ b) ⊎ (¬(a ≡ b))

-- show that natural numbers have decidable equality.
-- first, you need to prove the no-confusion principle: zero is not equal to suc.
-- hint: define a function Nat → Type that is equals ⊥ when the input is not zero, and use transport.
zero≠suc : ∀ {m} → (zero ≡ suc m) → ⊥
zero≠suc p = transport isZero p zero
  where
    isZero : Nat → Type
    isZero zero = Nat
    isZero (suc _) = ⊥

-- now show decidable equality of natural numbers.
-- you can use with-abstraction https://agda.readthedocs.io/en/latest/language/with-abstraction.html#with-abstraction
-- to help you.
eqDecNat : (n m : Nat) → (n ≡ m) ⊎ (¬(n ≡ m))
eqDecNat zero zero = inl refl
eqDecNat zero (suc m) = inr zero≠suc
eqDecNat (suc n) zero = inr (zero≠suc ∘ sym)
eqDecNat (suc n) (suc m) with (eqDecNat n m)
eqDecNat (suc n) (suc m) | inl p = inl (cong suc p)
eqDecNat (suc n) (suc m) | inr p = inr λ impos → p (cong pred impos)

-- we are ready to show that natural numbers is a set.

-- composing a≡b with b≡a is always refl.
cancel : {A : Type} {a b : A} (p : a ≡ b) → refl ≡ trans (sym p) p
cancel refl = refl

-- the key is noticing that any proof (p : a ≡ b) is equal to (eqDec a a) ⁻¹ ∙ (eqDec a b)
-- i.e. a normal form. then p = q by transitivity.

-- we state the normal form in terms of eqDeqA, a, b, p.
normalForm : {A : Type} (eqDecA : (a b : A) → (a ≡ b) ⊎ (¬ (a ≡ b))) (a b : A) (p : a ≡ b) → Type
normalForm eqDecA a b p with eqDecA a a | eqDecA a b
... | inl a≡a  | inl a≡b  = p ≡ trans (sym a≡a) a≡b
... | inl a≡a  | inr ¬a≡b = ⊥-elim (¬a≡b p)
... | inr ¬a≡a | _        = ⊥-elim (¬a≡a refl)

-- we show the normal form by path induction.
theNormalForm : {A : Type} (eqDecA : (a b : A) → (a ≡ b) ⊎ (¬ (a ≡ b))) (a b : A) (p : a ≡ b) → normalForm eqDecA a b p
theNormalForm eqDecA a .a refl with eqDecA a a
... | inl a≡a = cancel a≡a
... | inr ¬a≡a = ⊥-elim (¬a≡a refl)

eqDec→isSet : (A : Type) → (eqDecA : (a b : A) → (a ≡ b) ⊎ (¬(a ≡ b))) → isSet A
eqDec→isSet A eqDecA a b p q with eqDecA a a | eqDecA a b | theNormalForm eqDecA a b p | theNormalForm eqDecA a b q
... | inl a≡a | inl a≡b | p≡nf | q≡nf = trans p≡nf (sym q≡nf)
... | inr ¬a≡a | _ | _ | _ = ⊥-elim (¬a≡a refl)
... | _ | inr ¬a≡b | _ | _ = ⊥-elim (¬a≡b p)

natIsSet : isSet Nat
natIsSet = eqDec→isSet Nat eqDecNat

-- now show that UIP <-> K. Only one direction is needed, but the other is trivial.
hasK : Type → Type
hasK A = (a : A) → (p : a ≡ a) → p ≡ refl

isSet→hasK : {A : Type} → (isSet A → hasK A)
isSet→hasK isSetA a p = isSetA a a p refl

hasK→isSet : {A : Type} → (hasK A → isSet A)
hasK→isSet hasKA a b refl q = sym (hasKA a q)

-- now we should have K for Nat.
natHasK : hasK Nat
natHasK = isSet→hasK natIsSet
