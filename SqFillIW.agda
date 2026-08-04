{-# OPTIONS --cubical=no-glue #-}

open import Helper
open import SqFillDef

open import Agda.Builtin.Sigma
open import Agda.Builtin.Product

module SqFillIW where
  module IWTypes -- defines the indexed W-type, and its Sigma/inductive record representation
    {ℓX ℓS ℓP}
    {X : Type ℓX} -- the type of index (ℕ in Vec : ℕ → Type)
    (S : X → Type ℓS) -- the set of all constructors (0 ↦ ⊤, (suc _) ↦ A)
    (P : ∀ x → S x → Type ℓP) -- the number of recursive arguments given a constructor (what about hidden in arrows?)
    (inX : ∀ x (s : S x) → P x s → X) -- the index given a constructor
    where

    data IW (x : X) : Type (ℓX ⊔ ℓS ⊔ ℓP) where
      node : (s : S x) → (subtree : (p : P x s) → IW (inX x s p)) → IW x

    Subtree : ∀{x} (s : S x) → Type (ℓX ⊔ ℓS ⊔ ℓP)
    Subtree {x} s = (p : P x s) → IW (inX x s p)

    IWRep : (x : X) → Type (ℓX ⊔ ℓS ⊔ ℓP)
    IWRep x = Σ {ℓS} {ℓX ⊔ ℓS ⊔ ℓP} (S x) (λ s → Subtree s)

    -- toRep : ∀{x} IW x → IWRep x
    -- toRep (node s subtree) = s , subtree

    -- toIW : ∀{x} IWRep x → IW x
    -- toIW (s , subtree) = node s subtree

  open IWTypes public

  module IWPathTypes
    {ℓX ℓS ℓP}
    {X : Type ℓX}
    (S : X → Type ℓS)
    (P : ∀ x → S x → Type ℓP)
    (inX : ∀ x (s : S x) → (p : P x s) → X)
    where

    getShape : ∀{x} → IW S P inX x → S x
    getShape (node s _) = s

    getSubtree : ∀{x} → (w : IW S P inX x) → Subtree S P inX (getShape w)
    getSubtree (node _ subtree) = subtree

    getArity : ∀{x} → (w : IW S P inX x) → Type ℓP
    getArity {x} (node s _) = P x s

    -- toRepPath : ∀{x} {w w' : IW S P inX x} → w ≡ w' → toRep S P inX w ≡ toRep S P inX w'
    -- toRepPath {w = w@(node s subtree)} {w' = w'@(node s' subtree')} p i
    --   = λ x → {!getShape (p i) , ?!}

  module IWPath
    {ℓX ℓS ℓP}
    {X : Type ℓX}
    (S : X → Type ℓS)
    (P : ∀ x → S x → Type ℓP)
    (inX : ∀ x (s : S x) → (p : P x s) → X)
    where

    open IWPathTypes S P inX

    IndexCover : Type (ℓX ⊔ ℓS ⊔ ℓP)
    IndexCover = Σ X (λ x → IW S P inX x × IW S P inX x)

    ShapeCover : IndexCover → Type ℓS
    ShapeCover (x , w , w') = getShape w ≡ getShape w'

    ArityCover : (xww' : IndexCover) → (ps : ShapeCover xww') → Type ℓP
    ArityCover (x , w , w') _ = P x (getShape w')

    InXCover : (xww' : IndexCover) → (ps : ShapeCover xww') → (p : ArityCover xww' ps) → IndexCover
    InXCover (x , w , w') ps p =
      inX x (getShape w') p ,
      subst (Subtree S P inX) ps (getSubtree w) p ,
      getSubtree w' p

    Cover : ∀{x} (w w' : IW S P inX x) → Type (ℓX ⊔ ℓS ⊔ ℓP)
    Cover {x} w w' = IW ShapeCover ArityCover InXCover (x , w , w')

  module IWPathEquiv
    {ℓX ℓS ℓP}
    {X : Type ℓX}
    (S : X → Type ℓS)
    (P : ∀ x → S x → Type ℓP)
    (inX : ∀ x (s : S x) → (p : P x s) → X)
    where

    open IWPath S P inX
    open IWPathTypes S P inX

    record Iso {ℓa ℓb} (A : Type ℓa) (B : Type ℓb) : Type (ℓa ⊔ ℓb) where
      field
        fun : A → B
        inv : B → A
        sec : ∀ b → fun (inv b) ≡ b
        ret : ∀ a → inv (fun a) ≡ a

    open Iso

    _∙∙_∙∙_ : ∀{ℓ} {A : Type ℓ} {a b c d : A} → a ≡ b → b ≡ c → c ≡ d → a ≡ d
    (ab ∙∙ bc ∙∙ cd) i = hcomp {φ = i ∨ ~ i} (λ where
        j (i = i0) → ab (~ j)
        j (i = i1) → cd j) (bc i)


    infixr 30 _∙_
    _∙_ : ∀{ℓ} {A : Type ℓ} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
    ab ∙ bc = refl ∙∙ ab ∙∙ bc

    _∘_ : ∀{a b c} {A : Type a} {B : Type b} {C : Type c} (f : B → C) → (g : A → B) → A → C
    f ∘ g = λ a → f (g a)

    ≡⟨⟩-syntax : ∀{ℓ} {A : Type ℓ} (x : A) {y z} → x ≡ y → y ≡ z → x ≡ z
    ≡⟨⟩-syntax x p q = p ∙ q
    infixr 3 ≡⟨⟩-syntax
    syntax ≡⟨⟩-syntax x p q = x ≡⟨ p ⟩ q

    IsoComp : ∀{a b c} {A : Type a} {B : Type b} {C : Type c}
              → Iso B C → Iso A B → Iso A C
    IsoComp i j .fun = i .fun ∘ j .fun
    IsoComp i j .inv = j .inv ∘ i .inv
    IsoComp i j .sec c = {!i .sec !}
    IsoComp i j .ret = {!!}

    module IsoFunExt
      {ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
      (f g : (a : A) → B a)
      where

      funExt : (∀ x → f x ≡ g x) → f ≡ g
      funExt p i x = p x i

      funExt⁻ : f ≡ g → (a : A) → f a ≡ g a
      funExt⁻ p a i = p i a

      IsoFunExt : Iso (∀ x → f x ≡ g x) (f ≡ g)
      IsoFunExt .fun = funExt
      IsoFunExt .inv = funExt⁻
      IsoFunExt .sec b = refl
      IsoFunExt .ret a = refl

    open IsoFunExt

    module PathPIsoPath
      {ℓ} {A : I → Type ℓ} {a : A i0} {b : A i1}
      where

      fromPathP : PathP A a b → transport (λ i → A i) a ≡ b
      fromPathP p i = transp (λ j → A (i ∨ j)) i (p i)

      toPathP : transport (λ i → A i) a ≡ b → PathP A a b
      toPathP p i = hcomp (λ j → λ { (i = i0) → a ; (i = i1) → p j }) (transp (λ j → A (i ∧ j)) (~ i) a)

      PathPIsoPath : Iso (PathP A a b) (transport (λ i → A i) a ≡ b)
      PathPIsoPath .fun = fromPathP
      PathPIsoPath .inv = toPathP
      PathPIsoPath .sec = {!!}
      PathPIsoPath .ret p = {!!}

    open PathPIsoPath

    encode : ∀{x} w w' → Iso (w ≡ w') (Cover {x} w w')
    encodeSubtree :
      ∀{x} w w' (sc : ShapeCover (x , w , w'))
      → Iso (PathP (λ i → Subtree S P inX (sc i)) (getSubtree w) (getSubtree w'))
            ((p : ArityCover (x , w , w') sc) → IW ShapeCover ArityCover InXCover (InXCover (x , w , w') sc p))

    encodeSubtree w@(node s subtree) w'@(node s' subtree') sc .fun subp p
      = encode (subst (Subtree S P inX) sc subtree p) (subtree' p) .fun
               (funExt⁻
                 (subst (Subtree S P inX) sc subtree) subtree'
                 (fromPathP {A = λ i → Subtree S P inX (sc i)} {a = subtree}
                   {b = subtree'} subp)
                 p)
        where
          tmp = transport-filler (cong (Subtree S P inX) sc) subtree

    encode w@(node s subtree) w'@(node s' subtree') .fun wp
      = node (cong getShape wp) (encodeSubtree w w' (cong getShape wp) .fun (cong getSubtree wp))

    decode : ∀{x} w w' → Cover{x} w w' → w ≡ w'
    decodeSubtree :
      ∀{x} w w' (sc : ShapeCover (x , w , w'))
      → ((p : ArityCover (x , w , w') sc) → IW ShapeCover ArityCover InXCover (InXCover (x , w , w') sc p))
      → PathP (λ i → Subtree S P inX (sc i)) (getSubtree w) (getSubtree w')

    decode w@(node s subtree) w'@(node s' subtree') c@(node sc subtreec)
      = cong₂ node sc (decodeSubtree w w' sc subtreec)

    decodeSubtree w@(node s subtree) w'@(node s' subtree') cs subtreec
      = {!!}


  module IWSqFill
    {ℓX ℓS ℓP}
    {X : Type ℓX}
    (S : X → Type ℓS)
    (P : ∀ x → S x → Type ℓP)
    (inX : ∀ x (s : S x) → (p : P x s) → X)
    where

    open IWTypes

    SqFillIW : ∀{x} → SqFill (IW S P inX x)
    SqFillIW {x} {node s subtree} {node s₁ subtree₁} l {node s₂ subtree₂} {node s₃ subtree₃} r u d i j
      = {!
        (hcomp (λ where
            k (i = i0) → decodeEncodeW w0- k j
            k (i = i1) → decodeEncodeW w1- k j
            k (j = i0) → decodeEncodeW w-0 k i
            k (j = i1) → decodeEncodeW w-1 k i)
          -- (sup-W (SquareΣ i j .fst) (SquareΣ i j .snd))
          -- (sup-W (sqs i j) λ ps → {!!})
          (decodeSquare encodeWFilledSquare i j)
        )
      !}
