{-# OPTIONS --cubical=uip --type-in-type #-}

-- open import Agda.Builtin.Equality
open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical
  renaming ( primIMin       to _∧_  -- I → I → I
           ; primIMax       to _∨_  -- I → I → I
           ; primINeg       to ~_   -- I → I
           ; primComp       to comp
           ; primHComp      to hcomp
           ; primTransp     to transp
           ; itIsOne        to 1=1 )

open import Agda.Primitive renaming (Set   to Type)
open import Agda.Builtin.Cubical.Sub
  renaming (primSubOut to outS)
import Agda.Builtin.Cubical.HCompU

open import Helper hiding (sym)
open import SqFill using (SqFill)
primitive
  prim^sqFill : ∀{ℓ} (A : Type ℓ) → SqFill A
-- postulate prim^sqFill : (A : Set) → SqFill A
sqFill = prim^sqFill
uip : {A : Type} {x y : A} (p q : x ≡ y) → p ≡ q
uip p q = sqFill _ p q refl refl

sym : ∀ {ℓ} {A : Set ℓ} {a b : A} → a ≡ b → b ≡ a
sym p i = p (~ i)
{-# INLINE sym #-}

subst : ∀{ℓ ℓ'} {A : Type ℓ} {x y : A} (B : A → Type ℓ') (p : x ≡ y) → B x → B y
subst B p pa = transport (λ i → B (p i)) pa
{-# INLINE subst #-}

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


infixr 30 _∙_
_∙_ : ∀{ℓ} {A : Type ℓ} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
ab ∙ bc = refl ∙∙ ab ∙∙ bc

hfill : ∀{ℓ} {A : Type ℓ}
        {φ : I}
        (u : ∀ i → Partial φ A)
        (u0 : A [ φ ↦ u i0 ])
        -----------------------
        (i : I) → A
hfill {φ = φ} u u0 i =
  hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                 ; (i = i0) → outS u0 })
        (outS u0)

-- -- any two definitions of double composition are equal
-- compPath-unique : ∀{A} {w x y z : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
--                   → (α β : Σ (x ≡ w) (λ s → PathP (λ j → p (~ j) ≡ r j) q s))
--                   → α ≡ β
-- compPath-unique p q r (α , α-filler) (β , β-filler) t
--   = (λ i → cb i1 i) , (λ j i → cb j i)
--   where cb : I → I → _
--         cb j i = hfill (λ j → λ { (t = i0) → α-filler j i
--                                 ; (t = i1) → β-filler j i
--                                 ; (i = i0) → p (~ j)
--                                 ; (i = i1) → r j })
--                        (inS (q i)) j

reflIdr : ∀{ℓ} {A : Type ℓ} {a b : A} {p : a ≡ b} → p ∙ refl ≡ p
-- reflIdr {a = a} {b} {p} i j = hcomp
--   (λ { k (i = i0) → {!hfill (λ {l (j = i0) → a ; l (j = i1) → b}) (p k)!}
--      ; k (i = i1) → {!p k!}
--      ; k (j = i0) → a
--      ; k (j = i1) → b}) {!!}
-- reflIdr {a = a} {b} {p} i j = hfill (λ {i (j = i0) → a ; i (j = i1) → b}) (inS (p j)) (~ i)
reflIdr {a = a} {b} {p} = J (λ _ p → p ∙ refl ≡ p) (λ i j →  hfill (λ {i (j = i0) → a ; i (j = i1) → a}) (inS a) (~ i)) p

symInvr : ∀{ℓ} {A : Type ℓ} {a b : A} {p : a ≡ b} → p ∙ sym p ≡ refl
symInvr {a = a} {b} {p} = J (λ _ p → p ∙ sym p ≡ refl) ((λ i j →  hfill (λ {i (j = i0) → a ; i (j = i1) → a}) (inS a) (~ i))) p

symInvl : ∀{ℓ} {A : Type ℓ} {a b : A} {p : a ≡ b} → sym p ∙ p ≡ refl
symInvl {a = a} {b} {p} = J (λ _ p → sym p ∙ p ≡ refl) ((λ i j →  hfill (λ {i (j = i0) → a ; i (j = i1) → a}) (inS a) (~ i))) p

≡⟨⟩-syntax : ∀{ℓ} {A : Type ℓ} (x : A) {y z} → x ≡ y → y ≡ z → x ≡ z
≡⟨⟩-syntax x p q = p ∙ q
infixr 3 ≡⟨⟩-syntax
syntax ≡⟨⟩-syntax x p q = x ≡⟨ p ⟩ q

≡⟨⟨-syntax : ∀{ℓ} {A : Type ℓ} (x : A) {y z} → y ≡ z → x ≡ y → x ≡ z
≡⟨⟨-syntax x p q = q ∙ p
infixr 3 ≡⟨⟨-syntax
syntax ≡⟨⟨-syntax x p q = x ≡⟨ p ⟨ q

-- coe0→1 : {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) → A i0 → A i1
-- coe0→1 A = transp (λ i → A i) i0

coe0→i : {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i : I) → A i0 → A i
coe0→i A i = transp (λ j → A (i ∧ j)) (~ i)

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

functorFromPath' : {C D : Category} → C ≡ D → Functor C D
functorFromPath' {D = D} p = transport (λ i → Functor (p (~ i)) D) (idFunctor D)

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
functorFromPathInv p = {!functorFromPath!}

functorFromPathEq : ∀{C D} (p : C ≡ D) → functorFromPath p ≡ functorFromPath' p
functorFromPathEq = J (λ _ p' → functorFromPath p' ≡ functorFromPath' p') refl

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

idNatTransIdl : ∀{C D} {F G : Functor C D} (α : NatTrans F G) → idNatTrans F ⋆N α ≡ α
idNatTransIdl {D = D} α i .N-ob x =  D .⋆Idl (α .N-ob x) i 
idNatTransIdl {D = D} {F} {G} α i .N-hom {x} {y} f j =
  sqFill _ (λ j → (idNatTrans F ⋆N α) .N-hom f j) (λ j → α .N-hom f j) (λ i → (D ⋆ F .F-hom f) (D .⋆Idl (α .N-ob y) i)) (λ i → (D ⋆ D .⋆Idl (α .N-ob x) i) (G .F-hom f)) i j

idNatTransIdr : ∀{C D} {F G : Functor C D} (α : NatTrans F G) → α ⋆N idNatTrans G ≡ α
idNatTransIdr {D = D} α i .N-ob x =  D .⋆Idr (α .N-ob x) i
idNatTransIdr {D = D} {F} {G} α i .N-hom {x} {y} f j =
  sqFill _ (λ j → (α ⋆N idNatTrans G) .N-hom f j) (λ j → α .N-hom f j) (λ i → (D ⋆ F .F-hom f) (D .⋆Idr (α .N-ob y) i)) (λ i → (D ⋆ D .⋆Idr (α .N-ob x) i) (G .F-hom f)) i j

record NatIso {C D : Category} {F G : Functor C D} (ϕ : NatTrans F G): Set₁ where
  no-eta-equality
  field
    inv : NatTrans G F
    sec : inv ⋆N ϕ ≡ idNatTrans G
    ret : ϕ ⋆N inv ≡ idNatTrans F


idNatIso : ∀{C D} (F : Functor C D) → NatIso (idNatTrans F)
idNatIso F .NatIso.inv = idNatTrans F
idNatIso {D = D} F .NatIso.sec i .N-ob x = D .⋆Idl (D .⋆id) i
idNatIso {D = D} F .NatIso.sec i .N-hom {x} {y} f =
  let Ff = F .F-hom f in
    sqFill (D [ F .F-ob x , F .F-ob y ])
           ((idNatTrans F ⋆N idNatTrans F) .N-hom f)
           (D .⋆Idr Ff ∙ sym (D .⋆Idl Ff))
           (λ i → (D ⋆ Ff) (D .⋆Idl (D .⋆id) i))
           (λ i → (D ⋆ D .⋆Idl (D .⋆id) i) Ff) i
idNatIso F .NatIso.ret = idNatTransIdl _  

-- two functors F:C->D and G:D->C constitute an equiv of categories
-- if there exists two natural isomorphisms from GF to IDc and GF to IDd.
record ConstituteEquiv {C D : Category} (F : Functor C D) (G : Functor D C): Set₁ where
  no-eta-equality
  field
    ε : NatTrans (F ⋆F G) (idFunctor C)
    srcIso : NatIso ε
    η : NatTrans (G ⋆F F) (idFunctor D)
    tgtIso : NatIso η

record EquivCat (C D : Category) : Set₁ where
  no-eta-equality
  field
    F : Functor C D
    G : Functor D C
    isEquiv : ConstituteEquiv F G

idFunctorIdl : ∀{C D} (F : Functor C D) → idFunctor C ⋆F F ≡ F
idFunctorIdl F i .F-ob = F .F-ob
idFunctorIdl F i .F-hom = F .F-hom
idFunctorIdl {C} {D} F i .F-id = uip ((idFunctor C ⋆F F) .F-id) (F .F-id) i
idFunctorIdl {C} F i .func = uip ((idFunctor C ⋆F F) .func) (F .func) i

idFunctorIdr : ∀{C D} (F : Functor C D) → F ⋆F idFunctor D ≡ F
idFunctorIdr {C} {D} F i .F-ob = F .F-ob
idFunctorIdr {C} {D} F i .F-hom = F .F-hom
idFunctorIdr {C} {D} F i .F-id {x} = uip ((F ⋆F idFunctor D) .F-id) (F .F-id) i
idFunctorIdr {C} {D} F i .func = uip ((F ⋆F idFunctor D) .func) (F .func) i

transport∙ : ∀{ℓ} {A B C : Type ℓ} {a : A} (p : A ≡ B) (q : B ≡ C) → transport (λ i → (p ∙ q) i) a ≡ transport (λ i → q i) (transport (λ i → p i) a)
transport∙ {B = B} {C} {a} = J (λ B' p → (q : B' ≡ C) → transport (λ i → (p ∙ q) i) a ≡ transport (λ i → q i) (transport (λ i → p i) a))
                               (λ q → cong (transport (λ j → q j)) (cong (transport refl) (transportRefl _)))

natTransFromPath : ∀{C D} {F G : Functor C D} → F ≡ G → NatTrans F G
natTransFromPath {F = F} p = transport (λ i → NatTrans F (p i)) (idNatTrans F)

natTransFromPathRefl : ∀{C D} (F : Functor C D) → natTransFromPath (refl {x = F}) ≡ idNatTrans F
natTransFromPathRefl F = transportRefl _

natTransFromPath∙ : ∀{C D} {F G H : Functor C D} (p : F ≡ G) (q : G ≡ H) → natTransFromPath p ⋆N natTransFromPath q ≡ natTransFromPath (p ∙ q)
natTransFromPath∙ {G = G} p = J
                       (λ H' q →
                          (natTransFromPath p ⋆N natTransFromPath q) ≡
                          natTransFromPath (p ∙ q))
                       Jrefl
  where
    Jrefl : (natTransFromPath p ⋆N natTransFromPath refl) ≡ natTransFromPath (p ∙ refl)
    Jrefl  = natTransFromPath p ⋆N natTransFromPath refl ≡⟨ cong (_⋆N_ _) (natTransFromPathRefl _) ⟩
             natTransFromPath p ⋆N idNatTrans G          ≡⟨ idNatTransIdr _ ⟩
             cong natTransFromPath (sym reflIdr)
    -- Jrefl = J (λ G' p → (natTransFromPath p ⋆N natTransFromPath refl) ≡ natTransFromPath (p ∙ refl)) {!!} p
    --
functorFromPathRefl : ∀{C} → functorFromPath (refl {x = C}) ≡ idFunctor C
functorFromPathRefl = transportRefl _ 

functorFromPath∙ : ∀{C D E} (p : C ≡ D) (q : D ≡ E) → functorFromPath p ⋆F functorFromPath q ≡ functorFromPath (p ∙ q)
functorFromPath∙ {E = E} p = J
                       (λ _ q →
                          (functorFromPath p ⋆F functorFromPath q) ≡
                          functorFromPath (p ∙ q))
                       Jrefl
  where
    Jrefl : (functorFromPath p ⋆F functorFromPath refl) ≡ functorFromPath (p ∙ refl)
    Jrefl  = functorFromPath p ⋆F functorFromPath refl ≡⟨ cong (_⋆F_ _) functorFromPathRefl ⟩
             functorFromPath p ⋆F idFunctor _          ≡⟨ idFunctorIdr _ ⟩
             cong functorFromPath (sym reflIdr)


equivCatC : ∀{C} → EquivCat C C
equivCatC {C} .EquivCat.F = idFunctor C
equivCatC {C} .EquivCat.G = idFunctor C
equivCatC {C} .EquivCat.isEquiv .ConstituteEquiv.ε                  = natTransFromPath (idFunctorIdl _)
equivCatC {C} .EquivCat.isEquiv .ConstituteEquiv.srcIso .NatIso.inv = natTransFromPath (sym (idFunctorIdl _))
equivCatC {C} .EquivCat.isEquiv .ConstituteEquiv.srcIso .NatIso.sec =
  natTransFromPath _ ⋆N natTransFromPath _ ≡⟨ natTransFromPath∙ (sym (idFunctorIdl _)) (idFunctorIdl _) ⟩
  natTransFromPath _                       ≡⟨ cong natTransFromPath symInvl ⟩
  natTransFromPathRefl _
equivCatC {C} .EquivCat.isEquiv .ConstituteEquiv.srcIso .NatIso.ret =
  _ ⋆N _ ≡⟨ natTransFromPath∙ (idFunctorIdl _) (sym (idFunctorIdl _)) ⟩
  natTransFromPath _ ≡⟨ cong natTransFromPath symInvr ⟩
  natTransFromPathRefl _
equivCatC {C} .EquivCat.isEquiv .ConstituteEquiv.η = natTransFromPath (idFunctorIdl _)
equivCatC {C} .EquivCat.isEquiv .ConstituteEquiv.tgtIso .NatIso.inv = natTransFromPath (sym (idFunctorIdl _))
equivCatC {C} .EquivCat.isEquiv .ConstituteEquiv.tgtIso .NatIso.sec =
  natTransFromPath _ ⋆N natTransFromPath _ ≡⟨ natTransFromPath∙ (sym (idFunctorIdl _)) (idFunctorIdl _) ⟩
  natTransFromPath _                       ≡⟨ cong natTransFromPath symInvl ⟩
  natTransFromPathRefl _
equivCatC {C} .EquivCat.isEquiv .ConstituteEquiv.tgtIso .NatIso.ret =
  _ ⋆N _ ≡⟨ natTransFromPath∙ (idFunctorIdl _) (sym (idFunctorIdl _)) ⟩
  natTransFromPath _ ≡⟨ cong natTransFromPath symInvr ⟩
  natTransFromPathRefl _

equivCatFromPath : ∀{C D} (p : C ≡ D) → EquivCat C D
equivCatFromPath {C} p = transport (λ i → EquivCat C (p i)) equivCatC

constituteEquivFromPath-sym : ∀{C D} → (p : C ≡ D) → ConstituteEquiv (functorFromPath p) (functorFromPath (sym p))
constituteEquivFromPath-sym {C} {D} p = transport (cong (ConstituteEquiv _) (sym (functorFromPathEq (sym p)))) (equivCatFromPath p .EquivCat.isEquiv)

idFunctor≡functorFromPathRefl : ∀{C} → idFunctor C ≡ functorFromPath refl
idFunctor≡functorFromPathRefl {C} = sym (transportRefl _)

constituteEquivFromPath : ∀{C D} (p : C ≡ D) (q : D ≡ C) → ConstituteEquiv (functorFromPath p) (functorFromPath q)
constituteEquivFromPath p q = subst (λ x → ConstituteEquiv (functorFromPath p) (functorFromPath x)) (uip (sym p) q) (constituteEquivFromPath-sym p)

open import Agda.Builtin.Nat

TypeCat : Category
TypeCat .ob = Nat
TypeCat .Hom[_,_] = _≡_
TypeCat ._⋆_ = _∙_
TypeCat .⋆id = refl
TypeCat .⋆Idl = {!reflIdl!}
TypeCat .⋆Idr p = reflIdr
TypeCat .⋆Assoc = {!!}
TypeCat .isSetHom = {!!}

x = constituteEquivFromPath {C = TypeCat} refl refl .ConstituteEquiv.ε .N-ob 1
see : x ≡ refl
see = {!!}

module Equiv where

  id : ∀{ℓ} {A : Type ℓ} → A → A
  id a = a

  record qinv {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} (f : A → B) : Type (ℓa ⊔ ℓb) where
    field
      g : B → A
      sec : g ⋆f f ≡ id
      ret : f ⋆f g ≡ id

  record reallyIsEquiv {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} (f : A → B) : Type (ℓa ⊔ ℓb) where

module Adjoint where
  -- universal morphism
  -- record AdjointUniv {C D : Category} (L : Functor C D) (R : Functor D C) where
  --   field
  --     AdjUnivR :
  --       -- for any object c : C, there is a universal morphism from c to R.
  --       (c : C .ob) →
  --       -- ... in the sense that we have a special εc : C [ c , R L c ] such that
  --       (∃ (εc : C [ c , R L c ])
  --           -- any morphism from c C [ R d , c ] must factor through εc : C [ R L c , c ])
  --           -- Rd -> c
  --           -- RLc /
  --           -- ... that is, there exists a (g : )
  --          ({d : D .ob} (f : C [ R d , c ]) → ∃! (g : D [ d , R c ]) (f )))
  -- record AdjointHomIso {C D : Category} (L : Functor C D) (R : Functor D C) : Type₁ where
  --   field
  --     adj  : ∀{c d} → C [ c , R .F-ob d ] → D [ L .F-ob c , d ]
  --     adj' : ∀{c d} → D [ L .F-ob c , d ] → C [ c , R .F-ob d ]
  --     adj-bij : ∀{f} → (adj ∘f adj') f ≡ f

  -- record AdjointUnitCounit {C D : Category} (L : Functor C D) (R : Functor D C) : Type₁ where
  --   field
  --     η : NatTrans (idFunctor C) (R ∘F L)
  --     ε : NatTrans (L ∘F R) (idFunctor D)
  --     ▵L : (L η) ⋆N (ε L) ≡ idNatTrans L
  --     ▵R : (η R) ⋆N (R ε) ≡ idNatTrans R
