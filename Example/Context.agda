{-# OPTIONS --cubical=uip --guardedness #-}

module Example.Context where
open import Example.Category
open import Cubical.Foundations.Prelude using (_≡_; refl; cong; sym; _∙_)
open import Data.Unit using (⊤; tt)
open import Function using (id; _∘_)

record Ctx (C : Category) : Set₁ where
  open Category C
  field
    ctx-cell : Obj → Set
    ctx-hom  : {x y : Obj} → Hom x y → ctx-cell y → ctx-cell x
    ctx-id   : {x : Obj} {γ : ctx-cell x} → ctx-hom hom-id γ ≡ γ
    ctx-comp : {x y z : Obj} {f : Hom x y} {g : Hom y z} {γ : ctx-cell z}
             → ctx-hom (g · f) γ ≡ ctx-hom f (ctx-hom g γ)
  
open Ctx public renaming (ctx-cell to _⟨_⟩; ctx-hom to _⟪_⟫_)

module _ {C : Category} where
  infix 10 _⇒_
  infix 20 _⊚_
  open Category C
  private
    variable
      x y z : Obj
      Δ Γ Θ : Ctx C

  strong-ctx-comp : (Γ : Ctx C) {f : Hom x y} {g : Hom y z}
                    {γz : Γ ⟨ z ⟩} {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩}
                  → (eq-zy : Γ ⟪ g ⟫ γz ≡ γy) (eq-yx : Γ ⟪ f ⟫ γy ≡ γx)
                  → Γ ⟪ g · f ⟫ γz ≡ γx
  strong-ctx-comp Γ {f} {g} {γz} {γy} {γx} eq-zy eq-yx = (ctx-comp Γ) ∙ (cong (Γ ⟪ f ⟫_) eq-zy) ∙ eq-yx

  record _⇒_ (Δ : Ctx C) (Γ : Ctx C) : Set where
    field
      func       : {x : Obj} → Δ ⟨ x ⟩ → Γ ⟨ x ⟩
      naturality : {x y : Obj} {f : Hom x y} {δ : Δ ⟨ y ⟩}
                 → Γ ⟪ f ⟫ (func δ) ≡ func (Δ ⟪ f ⟫ δ)
  -- naturality condition for substitutions: let σ : Δ ⇒ Γ
  --
  --             func
  --     Δ(x) ----------> Γ(x)
  --      ∧                ∧
  --      |                |
  --      |Δ(f)            |Γ(f)
  --      |                |
  --      |                |
  -- δ ∈ Δ(y) ----------> Γ(y)
  --             func

  open _⇒_ public

  id-subst : (Γ : Ctx C) → Γ ⇒ Γ
  id-subst Γ .func = id
  id-subst Γ .naturality = refl


  -- composition of substitutions: let f : x → y (in Hom(C)), σ : Δ ⇒ Γ, τ : Γ → θ (in Psh(C))
  --
  --           func σ y         func τ y
  -- δ ∈ Δ(y) ----------> Γ(y) ----------> Θ(y)
  --      |                |                |
  --      |                |                |
  --      |Δ(f)            |Γ(f)            |Θ(f)
  --      |                |                |
  --      ∨                |                ∨
  --     Δ(x) ----------> Γ(x) ----------> Θ(x)
  --           func σ y         func τ y

  _⊚_ : Γ ⇒ Θ → Δ ⇒ Γ → Δ ⇒ Θ
  (τ ⊚ σ) .func = func τ ∘ func σ
  (τ ⊚ σ) .naturality = naturality τ ∙ cong (func τ) (naturality σ)
  
  ◇ : Ctx C
  ◇ ⟨ _ ⟩ = ⊤
  ◇ ⟪ _ ⟫ _ = tt
  ◇ .ctx-id = refl
  ◇ .ctx-comp = refl

  !◇ : (Γ : Ctx C) → Γ ⇒ ◇
  !◇ Γ .func _ = tt
  !◇ Γ .naturality _ = tt

  ◇-terminal : (Γ : Ctx C) (σ τ : Γ ⇒ ◇) → σ ≡ τ
  ◇-terminal Γ σ τ _ .func _ = tt
  ◇-terminal Γ σ τ _ .naturality = refl

