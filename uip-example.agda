{-# OPTIONS --cubical=uip #-}

-- open import Agda.Builtin.Equality
open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical
  renaming ( primIMin       to _∧_  -- I → I → I
           ; primIMax       to _∨_  -- I → I → I
           ; primINeg       to ~_   -- I → I
           ; primComp       to comp
           ; primHComp      to hcomp
           ; primTransp     to transp)

open import Agda.Primitive renaming (Set   to Type)
open import Agda.Builtin.Cubical.Sub

sym : ∀ {ℓ} {A : Set ℓ} {a b : A} → a ≡ b → b ≡ a
sym p i = p (~ i)

infixr 4 _$_ 
_$_ : ∀ {ℓa ℓb} {A : Set ℓa} {B : A → Set ℓb} (f : (a : A) → B a) (a : A) → B a
f $ a = f a
-- {-# INLINE _$_ #-}

_⋆f_ : ∀{ℓa ℓb ℓc} {A : Set ℓa} {B : Set ℓb} {C : Set ℓc} → (f : A → B) → (g : B → C) → A → C
f ⋆f g = λ a → g (f a)

_∘f_ : ∀{ℓa ℓb ℓc} {A : Set ℓa} {B : Set ℓb} {C : Set ℓc} → (f : B → C) → (g : A → B) → A → C
f ∘f g = g ⋆f f

record Category : Set₁ where 
  no-eta-equality
  infixl 5 _∘_
  infixl 5 _⋆_
  field 
    ob : Set
    Hom[_,_] : ob → ob → Set
    _⋆_ : ∀{x y z} → (f : Hom[ x , y ]) (g : Hom[ y , z ]) → Hom[ x , z ]
    ⋆id : ∀{x} → Hom[ x , x ]
    ⋆Idl : ∀{x y} (f : Hom[ x , y ]) → ⋆id ⋆ f ≡ f
    ⋆Idr : ∀{x y} (f : Hom[ x , y ]) → f ⋆ ⋆id ≡ f
    ⋆Assoc : ∀{w x y z} {f : Hom[ w , x ]} {g : Hom[ x , y ]} {h : Hom[ y , z ]}
            → f ⋆ (g ⋆ h) ≡ f ⋆ g ⋆ h
    isSetHom : ∀ {x y} {f g : Hom[ x , y ]} (p q : f ≡ g) → p ≡ q
  
  _∘_ : ∀ {x y z} → Hom[ y , z ] → Hom[ x , y ] → Hom[ x , z ]
  f ∘ g = g ⋆ f

open Category

_[_,_] : (C : Category) → C .ob → C .ob → Set
_[_,_] = Hom[_,_]

seq' : (C : Category) {x y z : C .ob} (f : C [ x , y ]) (g : C [ y , z ]) → C [ x , z ]
seq' = _⋆_
syntax seq' C f g = f ⋆⟨ C ⟩ g
infixl 5 seq'
comp' : (C : Category) {x y z : C .ob} (f : C [ y , z ]) (g : C [ x , y ]) → C [ x , z ]
comp' = _∘_
{-# INLINE comp' #-}
syntax comp' C f g = f ∘⟨ C ⟩ g
infixl 5 comp'

record Functor (C D : Category) : Set₁ where
  no-eta-equality
  open Category
  field
    F-ob  : C .ob → D .ob
    F-hom : ∀{x y} (f : C [ x , y ]) → D [ F-ob x , F-ob y ]
    F-id : ∀{x} → F-hom (C .⋆id) ≡ D .⋆id {x = (F-ob x)}
    func : ∀{x y z} {f : C [ x , y ]} {g : C [ y , z ]} 
            → F-hom (f ⋆⟨ C ⟩ g) ≡ (F-hom f) ⋆⟨ D ⟩ (F-hom g)
  
  -- isFull = (x y : _) (F[f] : D [ F-ob x , F-ob y ]) → 
open Functor

record NatTrans {C D : Category} (F G : Functor C D) : Set₁ where
  no-eta-equality
  field
    N-ob  : (x : C .ob) → D [ F .F-ob x , G .F-ob x ]
    -- naturality
    {-
      Fx --Ff-- Fy
      |         |
      N-ob x    N-ob y
      |         |
      Gx --Gf-- Gy
     -}
    N-hom : ∀{x y} (f : C [ x , y ]) 
            → F .F-hom f ⋆⟨ D ⟩ N-ob y ≡ N-ob x ⋆⟨ D ⟩ G .F-hom f
open NatTrans

_^op : Category → Category
(C ^op) .ob           = C .ob
(C ^op) .Hom[_,_] x y = C [ y , x ]
(C ^op) ._⋆_ f g = g ⋆⟨ C ⟩ f
(C ^op) .⋆id = C .⋆id
(C ^op) .⋆Idl = C .⋆Idr
(C ^op) .⋆Idr = C .⋆Idl
(C ^op) .⋆Assoc = sym (C .⋆Assoc)
(C ^op) .isSetHom = C .isSetHom

opop : {C : Category} → C ^op ^op ≡ C
opop {C} i .ob = C .ob
opop {C} i .Hom[_,_] = Hom[_,_] C
opop {C} i ._⋆_ = _⋆_ C
opop {C} i .⋆id = C .⋆id
opop {C} i .⋆Idl = C .⋆Idl
opop {C} i .⋆Idr = C .⋆Idr
opop {C} i .⋆Assoc = C .⋆Assoc
opop {C} i .isSetHom = C .isSetHom

record isIso {C : Category} {x y : C .ob} (f : C [ x , y ]) : Type where
  no-eta-equality
  field
    inv : C [ y , x ]
    -- section: chooses a point from each fibre to map from. 
    -- Happens FIRST i.e. on the left in a diagram
    sec : inv ⋆⟨ C ⟩ f ≡ C .⋆id 
    -- retraction: retracts from a larger space back: happense LATER, i.e. on the right in a diagram.
    ret : f ⋆⟨ C ⟩ inv ≡ C .⋆id
    
injective : ∀ {ℓa ℓb} {A : Set ℓa} {B : Set ℓb} (f : A → B) → Set _
injective {A = A} f = (a a' : A) → f a ≡ f a' → a ≡ a'

open import Agda.Builtin.Sigma

surjective : ∀ {ℓa ℓb} {A : Set ℓa} {B : Set ℓb} (f : A → B) → Set _
surjective {A = A} {B = B} f = (b : B) → Σ A (λ a → f a ≡ b)


-- record EquivCat (C D : Category) : Set₁ where
--   no-eta-equality
--   field
--     F : Functor C D
--     isFullyFaithful : FullyFaithful F
--     isEssSurj : EssSurj F

_∙∙_∙∙_ : ∀{ℓ} {A : Type ℓ} {a b c d : A} → a ≡ b → b ≡ c → c ≡ d → a ≡ d
(ab ∙∙ bc ∙∙ cd) i = hcomp {φ = i ∨ ~ i} (λ where
    j (i = i0) → ab (~ j)
    j (i = i1) → cd j) (bc i)

open import Helper hiding (sym)

infixr 30 _∙_
_∙_ : ∀{ℓ} {A : Type ℓ} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
ab ∙ bc = refl ∙∙ ab ∙∙ bc

≡⟨⟩-syntax : ∀{ℓ} {A : Type ℓ} (x : A) {y z} → x ≡ y → y ≡ z → x ≡ z
≡⟨⟩-syntax x p q = p ∙ q
infixr 3 ≡⟨⟩-syntax
syntax ≡⟨⟩-syntax x p q = x ≡⟨ p ⟩ q


-- coe0→1 : {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) → A i0 → A i1
-- coe0→1 A = transp (λ i → A i) i0

-- coe0→i : {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i : I) → A i0 → A i
-- coe0→i A i = transp (λ j → A (i ∧ j)) (~ i)


-- -- CoeFunctor : {C D : Category} → C ≡ D → Functor C D
-- -- CoeFunctor p .Functor.Fob = transport (λ i → p i .ob)
-- -- CoeFunctor p .Functor.Fhom {A} {B} = 
-- --   transport (λ i → p i .hom (coe0→i (λ i → p i .ob) i A)
-- --                             (coe0→i (λ i → p i .ob) i B))
-- -- CoeFunctor p .Functor.func {f = f} {g = g} = 
-- --   {! transport (λ i → (p i ._∘_) ? ?) !}
-- --   -- seems really complicated?

idFunctor : (C : Category) → Functor C C
idFunctor C .F-ob = λ z → z
idFunctor C .F-hom = λ f → f
idFunctor C .F-id = refl
idFunctor C .func = refl

functorFromPath : {C D : Category} → C ≡ D → Functor C D
functorFromPath {C} p = transport (λ i → Functor C (p i)) (idFunctor C)


functorComp : {C D E : Category} → Functor D E → Functor C D → Functor C E
functorComp G F .F-ob = (G .F-ob) ∘f (F .F-ob)
functorComp G F .F-hom = (G .F-hom) ∘f (F .F-hom)
functorComp G F .F-id = cong (G .F-hom) (F .F-id) ∙ G .F-id
functorComp G F .func = cong (G .F-hom) (F .func) ∙ G .func

_∘F_ : {C D E : Category} → Functor D E → Functor C D → Functor C E
_∘F_ = functorComp

_⋆F_ : {C D E : Category} → Functor C D → Functor D E → Functor C E
F ⋆F G = G ∘F F
infixl 30 _⋆F_

functorFromPathInv : ∀{C D} → (p : C ≡ D) → functorFromPath p ⋆F functorFromPath (sym p) ≡ idFunctor C
functorFromPathInv p i .F-ob = {!  !}
functorFromPathInv p i .F-hom = {!  !}
functorFromPathInv p i .F-id = {!  !}
functorFromPathInv p i .func = {!  !}

-- open Functor
-- open EquivCat
-- open FullyFaithful
-- CoeEquiv : {C D : Category} → C ≡ D → EquivCat C D
-- CoeEquiv p .F = CoeFunctor p
-- CoeEquiv p .isFullyFaithful .isFull a a' p' = {!  !}
-- CoeEquiv p .isFullyFaithful .isFaithful = {!  !}
-- CoeEquiv p .isEssSurj = {!  !}
-- -- really hard...


-- natural isomorphisms are natural transformations that compose to identity nat trans.
-- we have to first define 1. nat trans comp and 2. id nat trans.

natTransComp : {C D : Category} {F G H : Functor C D} (α : NatTrans G H) (β : NatTrans F G) → NatTrans F H
natTransComp {D = D} α β .N-ob x = α .N-ob x ∘⟨ D ⟩ β .N-ob x
natTransComp {D = D} {F = F} {G = G} α β .N-hom {x} {y} f = 
  let Ff = F .F-hom f ; Gf = G .F-hom f
      αx = α .N-ob x ; βx = β .N-ob x
      αy = α .N-ob y ; βy = β .N-ob y
  in
  Ff ⋆⟨ D ⟩ (αy ∘⟨ D ⟩ βy) ≡⟨ D .⋆Assoc ⟩ 
  Ff ⋆⟨ D ⟩ βy ⋆⟨ D ⟩ αy ≡⟨ cong (λ f → f ⋆⟨ D ⟩ αy) (β .N-hom f) ⟩ -- TODO: infer the cong automatically
  βx ⋆⟨ D ⟩ Gf ⋆⟨ D ⟩ αy ≡⟨ sym (D .⋆Assoc) ⟩ 
  βx ⋆⟨ D ⟩ (Gf ⋆⟨ D ⟩ αy) ≡⟨ cong (λ f → βx ⋆⟨ D ⟩ f) (α .N-hom f) ⟩ 
  D .⋆Assoc

_∘N_ : {C D : Category} {F G H : Functor C D} (α : NatTrans G H) (β : NatTrans F G) → NatTrans F H
_∘N_ = natTransComp

_⋆N_ : {C D : Category} {F G H : Functor C D} (β : NatTrans F G) (α : NatTrans G H) → NatTrans F H
β ⋆N α = α ∘N β

idNatTrans : {C D : Category} (F : Functor C D) → NatTrans F F
idNatTrans {D = D} F .N-ob x = D .⋆id
idNatTrans {D = D} F .N-hom f = D .⋆Idr (F .F-hom f) ∙ sym (D .⋆Idl (F .F-hom f))

record NatIso {C D : Category} {F G : Functor C D} (ϕ : NatTrans F G): Set₁ where
  no-eta-equality
  field
    inv : NatTrans G F
    sec : inv ⋆N ϕ ≡ idNatTrans G
    ret : ϕ ⋆N inv ≡ idNatTrans F

open import SqFill
primitive prim^sqFill : (A : Set) → SqFill A
sqFill = prim^sqFill

idNatIso : ∀{C D} (F : Functor C D) → NatIso (idNatTrans F)
idNatIso F .NatIso.inv = idNatTrans F
idNatIso {D = D} F .NatIso.sec i .N-ob x = D .⋆Idl (D .⋆id) i
idNatIso {D = D} F .NatIso.sec i .N-hom {x} {y} f j =
  let Ff = F .F-hom f in
  {! sqFill (D [ F .F-ob x , F .F-ob y ]) ((idNatTrans F ⋆N idNatTrans F) .N-hom f) ? (cong (λ f → Ff ⋆⟨ D ⟩ f) (D .⋆Idl (D .⋆id))) (D .⋆Idr Ff ∙ sym (D .⋆Idl Ff)) i j !}
  -- sqFill (D [ F .F-ob x , F .F-ob y ]) {F .F-hom f} {F .F-hom f} {!refl  !} {a₁₀ = F .F-hom f} {a₁₁ = F .F-hom f} _ _ _ i j
idNatIso F .NatIso.ret = {!  !}
  
-- two functors F:C->D and G:D->C constitute an equiv of categories
-- if there exists two natural isomorphisms from GF to IDc and GF to IDd.
record ConstituteEquiv {C D : Category} (F : Functor C D) (G : Functor D C): Set₁ where
  no-eta-equality
  field
    ε : NatTrans (F ⋆F G) (idFunctor C)
    srcIso : NatIso ε
    η : NatTrans (G ⋆F F) (idFunctor D)
    tgtIso : NatIso η

-- actually what's important is this function
-- natTransFromPath : ∀{C D} {F G : Functor C D} → F ≡ G → NatTrans F G
-- natTransFromPath p .N-ob = {!  !}
-- natTransFromPath p .N-hom = {!  !}

natTransFromPath : ∀{C D} {F G : Functor C D} → F ≡ G → NatTrans F G
natTransFromPath {F = F} p = transport (λ i → NatTrans F (p i)) (idNatTrans F)

-- J : ∀{ℓ} (A : Type ℓ) → (a : A) → (P : (b : A) → (a ≡ b) → Type) → P a refl → (b : A) → (p : a ≡ b) → P b p

constituteEquivFromPath : ∀{C D} → (p : C ≡ D) → ConstituteEquiv (functorFromPath p) (functorFromPath (sym p))
-- -- again, giving components amounts to certain hell.
-- constituteEquivFromPath {C} p .ConstituteEquiv.ε .N-ob x = {!  !}
-- constituteEquivFromPath p .ConstituteEquiv.ε .N-hom = {!  !}
-- constituteEquivFromPath p .ConstituteEquiv.srcIso = {!  !}
-- constituteEquivFromPath p .ConstituteEquiv.η = {!  !}
-- constituteEquivFromPath p .ConstituteEquiv.tgtIso = {!  !}
constituteEquivFromPath {C} p =
  J (λ _ p → ConstituteEquiv (functorFromPath p) (functorFromPath (sym p))) Prefl p
  where
    Prefl : ConstituteEquiv (functorFromPath refl) (functorFromPath (sym refl))
    Prefl .ConstituteEquiv.ε .N-ob x =
      transport (cong (λ a → C [ a , x ]) {!!}) {!!}
    Prefl .ConstituteEquiv.ε .N-hom = {!  !}
    Prefl .ConstituteEquiv.srcIso = {!  !}
    Prefl .ConstituteEquiv.η = {!  !}
    Prefl .ConstituteEquiv.tgtIso = {!  !}
