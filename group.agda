{-# OPTIONS --cubical=uip #-}

open import Agda.Builtin.Cubical.Path

module group where


record Group (A : Set) : Set₁ where
  infix 6 _⁻¹
  infixl 5 _∙_
  field
    id : A
    _⁻¹ : A → A
    _∙_ : A → A → A
    idl : ∀ {g} → id ∙ g ≡ g
    idr : ∀ {g} → g ∙ id ≡ g
    assoc∙ : ∀ {a b c} → a ∙ b ∙ c ≡ a ∙ (b ∙ c)
    invl : ∀ {g} → g ⁻¹ ∙ g ≡ id
    invr : ∀ {g} → g ∙ g ⁻¹ ≡ id


record GroupHom (A B : Set) (G : Group A) (H : Group B) : Set where
  private
    module G = Group G
    module H = Group H
  field
    f : A → B
    homid : f G.id ≡ H.id
    hom∙ : ∀ {a b} → (f a) H.∙ (f b) ≡ f (a G.∙ b)
