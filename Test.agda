{-# OPTIONS --cubical=uip #-}
{-# OPTIONS -v cubical.prim.uip:70 #-}

open import Agda.Primitive using () renaming (Set to Type)
open import Agda.Primitive.Cubical public
  renaming ( primIMin       to _∧_  -- I → I → I
           ; primIMax       to _∨_  -- I → I → I
           ; primINeg       to ~_   -- I → I
           ; isOneEmpty     to empty
           ; primComp       to comp
           ; primHComp      to hcomp
           ; primTransp     to transp
           ; itIsOne        to 1=1 )
open import Agda.Primitive.Cubical public
open import Agda.Builtin.Cubical.Path public
open import Agda.Builtin.Sigma

-- open import Cubical.Data.Empty.Base

open import SqFill
-- open import SqPFill

-- primitive primIMin : I → I → I
primitive
  prim^sqFill : (A : Type) → SqFill A

sqFill = prim^sqFill

module hello (A B : Type) where
  p : SqFill (A → B)
  p = prim^sqFill (A → B)

  postulate SqFillB : SqFill B

  q = SqFill.SqFillPi.SqFillPiAB A (λ ^ → B) (λ _ → sqFill B)

  check : (λ {lu} {ld} → p {lu} {ld}) ≡ q
  check k = p

module hello-dep (A : Type) (B : A → Type)
  where
  piPrim : SqFill ((a : A) → B a)
  piPrim = sqFill ((a : A) → B a)

  piManual : SqFill ((a : A) → B a)
  piManual = SqFill.SqFillPi.SqFillPiAB A (λ a → B a) (λ a → sqFill (B a))

  checkPi : (λ {lu} {ld} → piPrim {lu} {ld}) ≡ piManual
  checkPi _ = piPrim

  sigmaPrim : SqFill (Σ A (λ a → B a))
  sigmaPrim = {! sqFill (Σ A (λ a → B a)) !}

  -- productPrim : SqFill (Σ A (λ _ → A))
  -- productPrim = {! sqFill (Σ A (λ _ → A)) !}

  sigmaManual : SqFill (Σ A (λ a → B a))
  sigmaManual = SqFill.SqFillSigma.SqFillSigmaAB A (sqFill A) B λ a → sqFill (B a)

  checkSigma : (λ {lu} {ld} → sigmaPrim {lu} {ld}) ≡ sigmaManual
  checkSigma _ = sigmaPrim

  open import Agda.Builtin.Unit

  unitPrim : SqFill ⊤
  unitPrim = sqFill ⊤

  unitManual : SqFill ⊤
  unitManual = SqFill.SqFillUnit.SqFillUnit

  checkUnit : (λ {lu} {ld} → unitPrim {lu} {ld}) ≡ unitManual
  checkUnit _ = unitPrim

  open import Agda.Builtin.Bool

  boolPrim : SqFill Bool
  boolPrim = sqFill Bool

  boolManual : SqFill Bool
  boolManual = SqFill.SqFillBool.SqFillBool

  checkBool : (λ {lu} {ld} → boolPrim {lu} {ld}) ≡ boolManual
  checkBool _ = boolPrim

  ty : Type
  ty = ((⊤ → ⊤) → Σ Bool (λ{true → ⊤; false → Bool}))

  tm : ty
  -- tm = λ z → true , z tt
  tm = λ z → false , false

  adv : SqFill ty
  adv = sqFill _

  open import Helper using (refl)

  sq = adv {tm} {tm} refl {tm} {tm} refl refl refl

  test : sq ≡ refl
  test k i j =  λ z → false , false 

  tySigma : Type
  tySigma = Σ A (λ a → B a)

  postulate
    a : A
    b : B a
    C : (f : (a : A) → B a) → Type

  tmSigma : tySigma
  tmSigma = (a , b)

  advSigma : SqFill tySigma
  advSigma =  sqFill tySigma 

  sqSigma = advSigma {tmSigma} refl refl refl refl

  testSigma : sqSigma ≡ refl
  testSigma _ _ _ = {!a , b!}

  ty' = Σ ((a : A) → B a) (λ f → C f)

  tm' : ty'
  tm' = ({!!} , {!!})

  sqty' = sqFill ty' {tm'} refl refl refl refl

  testty' : sqty' ≡ refl
  testty' _ _ _ = {! ,!}

  tyProduct : Type
  tyProduct = Σ A (λ _ → A)

  tmProduct : tyProduct
  tmProduct = (a , a)

  advProduct : SqFill tyProduct
  advProduct =  sqFill tyProduct

  sqProduct = advProduct {tmProduct} refl refl refl refl

  testProduct : sqProduct ≡ refl
  testProduct _ _ _ = {!a , b!}

  -- open import Agda.Builtin.Nat

  -- NN : Type
  -- NN = Nat × Nat

  -- ℤ : Type
  -- ℤ = Σ NN (λ{(n , m) → (k : Nat) → n + k ≡ m + k})

  -- evaluate: try it on the projects we listed on TYPES abstract,
  --   rephrase in our primitives in necessary.
  -- theoretical: is our system canonical? maybe look into how hcomp for inductive types work.
  -- propose some venues for submitting this as a paper
