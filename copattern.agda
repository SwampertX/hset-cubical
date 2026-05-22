open import Agda.Builtin.Equality

module copattern where
  record Monoid (A : Set) : Set₁ where
    field
      id : A
      _∙_ : A → A → A
      idl : ∀ {a} → id ∙ a ≡ a
      assoc : ∀ {a b c} → (a ∙ b) ∙ c ≡ a ∙ (b ∙ c)

  open import Agda.Builtin.Nat

  open Monoid

  sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
  sym refl = refl

  cong : {A B : Set} {a b : A} (f : A → B) → a ≡ b → f a ≡ f b
  cong f refl = refl

  -- how to prove equality of non-eta records?
  natMonoid : Monoid Nat
  natMonoid .id = zero
  natMonoid ._∙_ = _+_
  natMonoid .idl = refl
  natMonoid .assoc {zero} = refl
  natMonoid .assoc {suc a} = cong suc (natMonoid .Monoid.assoc {a})

  natMonoid' : Monoid Nat
  natMonoid' .id = zero
  natMonoid' ._∙_ = _+_
  natMonoid' .idl = refl
  natMonoid' .assoc {zero} {b = zero} = sym refl
  natMonoid' .assoc {suc zero} {b = zero} {zero} = sym (cong suc refl)
  natMonoid' .assoc {suc (suc a)} {b = zero} {zero} = sym (cong suc (cong suc {!!}))
  natMonoid' .assoc {suc a} {b = zero} {suc c} = sym (cong suc {!!})
  natMonoid' .assoc {b = suc b} = {!!}
