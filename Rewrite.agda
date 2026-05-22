{-# OPTIONS --cubical --rewriting -v rewriting:40 #-}
-- {-# OPTIONS --cubical=uip --rewriting -v rewriting:90 -v tc.conv.face:40 -v tc.cover.iapply:40 #-}
-- {-# OPTIONS -v cubical.prim.uip:70 #-}  -- uncomment for debugging

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
-- open import Agda.Builtin.Coproduct
-- open import Agda.Builtin.Product
open import Helper using (refl)
open import Agda.Builtin.List
open import Agda.Builtin.Maybe

-- open import Cubical.Data.Empty.Base

open import SqFill

postulate _↦_ : ∀ {a} {A : Set a} → A → A → Set a
{-# BUILTIN REWRITE _↦_ #-}
-- sqFill (A → B) : SqFill (A → B)
-- sqFillPiAB A B sqFillB : SqFill (A → B)
postulate
  sqFill : (A : Type) → SqFill A
  -- rewritePi : ∀ {A B lu ld} → (sqFillB : (a : A) → SqFill (B a)) → sqFill ((a : A) → B a) {lu} {ld} ↦ SqFill.SqFillPi.SqFillPiAB A B sqFillB
  rewritePi : ∀ {A B sqFillB} → sqFill ((a : A) → B a) ↦ SqFill.SqFillPi.SqFillPiAB A B sqFillB

module hello (A : Type) (B : A → Type) where
  p : SqFill ((a : A) → B a)
  p = sqFill ((a : A) → B a)

  postulate sqFillB : (a : A) → SqFill (B a)

  rewritePi' : sqFill ((a : A) → B a) ↦ SqFill.SqFillPi.SqFillPiAB A B sqFillB
  rewritePi' = rewritePi {A = A} {B = B} {sqFillB = sqFillB}
  {-# REWRITE rewritePi' #-}

  q : SqFill ((a : A) → B a)
  q = SqFill.SqFillPi.SqFillPiAB A B sqFillB

  check : A → p ≡ q
  check _ k = p
  --
  --
module hello2 (A : Type) (B : A → Type) where
  p : SqFill ((a : A) → B a)
  p = sqFill ((a : A) → B a)

  -- postulate sqFillB : (a : A) → SqFill (B a)

  q : SqFill ((a : A) → B a)
  q = SqFill.SqFillPi.SqFillPiAB A B (hello.sqFillB A B)

  check : p ≡ q
  -- check k = {!p!}
  check k = p

-- module hello' where
--   postulate
--     A : Type
--     B : A → Type
--   p : SqFill ((a : A) → B a)
--   p = sqFill ((a : A) → B a)

--   postulate sqFillB : (a : A) → SqFill (B a)

--   rewritePi' = rewritePi {sqFillB = sqFillB}
--   {-# REWRITE rewritePi' #-}

--   q : SqFill ((a : A) → B a)
--   q = SqFill.SqFillPi.SqFillPiAB A B sqFillB

--   check : p ≡ q
--   check k = p

-- primitive primIMin : I → I → I
-- primitive
--   prim^sqFill : (A : Type) → SqFill A

-- sqFill = prim^sqFill

-- module hello (A B : Type) where
--   p : SqFill (A → B)
--   p = prim^sqFill (A → B)

--   postulate SqFillB : SqFill B

--   q = SqFill.SqFillPi.SqFillPiAB A (λ ^ → B) (λ _ → sqFill B)

--   check : (λ {lu} {ld} → p {lu} {ld}) ≡ q
--   check k = p

-- module hello-dep (A : Type) (B : A → Type)
--   where
--   piPrim : SqFill ((a : A) → B a)
--   piPrim = sqFill ((a : A) → B a)

--   piManual : SqFill ((a : A) → B a)
--   piManual = SqFill.SqFillPi.SqFillPiAB A (λ a → B a) (λ a → sqFill (B a))

--   checkPi : (λ {lu} {ld} → piPrim {lu} {ld}) ≡ piManual
--   checkPi _ = piPrim

--   sigmaPrim : SqFill (Σ A (λ a → B a))
--   sigmaPrim =  sqFill (Σ A (λ a → B a))

--   sigmaManual : SqFill (Σ A (λ a → B a))
--   sigmaManual = SqFill.SqFillSigma.SqFillSigmaAB A (sqFill A) B λ a → sqFill (B a)

--   checkSigma : (λ {lu} {ld} → sigmaPrim {lu} {ld}) ≡ sigmaManual
--   checkSigma _ = sigmaPrim

--   productPrim : SqFill (A × A)
--   productPrim =  sqFill (A × A)

--   productManual : SqFill (A × A)
--   productManual = SqFill.SqFillProduct.SqFillProductAB A (sqFill A) A (sqFill A)

--   checkProduct : (λ {lu} {ld} → productPrim {lu} {ld}) ≡ productManual
--   checkProduct i = productPrim

--   open import Agda.Builtin.Unit

--   unitPrim : SqFill ⊤
--   unitPrim = sqFill ⊤

--   unitManual : SqFill ⊤
--   unitManual = SqFill.SqFillUnit.SqFillUnit

--   checkUnit : (λ {lu} {ld} → unitPrim {lu} {ld}) ≡ unitManual
--   checkUnit _ = unitPrim

--   open import Agda.Builtin.Bool

--   boolPrim : SqFill Bool
--   boolPrim = sqFill Bool

--   boolManual : SqFill Bool
--   boolManual = SqFill.SqFillBool.SqFillBool

--   checkBool : (λ {lu} {ld} → boolPrim {lu} {ld}) ≡ boolManual
--   checkBool _ = boolPrim

--   ty : Type
--   ty = ((⊤ → ⊤) → Σ Bool (λ{true → ⊤; false → Bool}))

--   tm : ty
--   -- tm = λ z → true , z tt
--   tm = λ z → false , false

--   adv : SqFill ty
--   adv = sqFill ty

--   sq = adv {tm} {tm} refl {tm} {tm} refl refl refl

--   test : sq ≡ refl
--   test k i j =  λ z → false , false

--   tySigma : Type
--   tySigma = Σ A (λ a → B a)

--   postulate
--     a : A
--     b : B a
--     C : (f : (a : A) → B a) → Type

--   tmSigma : tySigma
--   tmSigma = (a , b)

--   advSigma : SqFill tySigma
--   advSigma =  sqFill tySigma

--   sqSigma = advSigma {tmSigma} refl refl refl refl

--   -- testSigma : sqSigma ≡ refl
--   -- testSigma _ _ _ = {!a , b!}

--   postulate
--     a1 a2 : A
--     p : a1 ≡ a2
--     b1 : B a1
--     b2 : B a2

--   tyPathP : Type
--   tyPathP = PathP (λ i → B (p i)) b1 b2

--   postulate tmPathP : tyPathP

--   sqPathP = sqFill tyPathP {tmPathP} refl refl refl refl

--   pathPPrim : SqFill tyPathP
--   pathPPrim = sqFill tyPathP

--   pathPManual : SqFill tyPathP
--   pathPManual = SqFill.SqFillPathP.SqFillPathP (B a1) (B a2) b1 b2 (λ i → B (p i)) (sqFill (B a1))

--   checkPathP : (λ {lu} {ld} → pathPPrim {lu} {ld}) ≡ pathPManual
--   checkPathP i {lu} {ld} = pathPPrim {lu} {ld}
--   -- testPathP : sqPathP ≡ refl
--   -- testPathP _ _ _ = {!tmPathP!}

--   -- tyPath = a ≡ a
--   sqPath = sqFill (a ≡ a) {refl {x = a}} refl refl refl refl
--   -- testPath : sqPath ≡ refl
--   -- testPath _ _ _ = {!refl!}

--   pathPrim : SqFill (a ≡ a)
--   pathPrim = sqFill (a ≡ a)

--   pathManual : SqFill (a ≡ a)
--   -- pathManual = SqFill.SqFillPathP.SqFillPathP A A a a (λ _ → A) (sqFill A)
--   pathManual = SqFill.SqFillPath.SqFillPath A a a (sqFill A)

--   checkPath : (λ {lu} {ld} → pathPrim {lu} {ld}) ≡ pathManual
--   checkPath i {lu} {ld} = pathPrim {lu} {ld}

--   coproductPrim : SqFill (A ⊎ A)
--   coproductPrim = sqFill (A ⊎ A)

--   coproductManual : SqFill (A ⊎ A)
--   coproductManual = SqFill.SqFillCoproduct.SqFillCoproduct A (sqFill A) A (sqFill A)

--   checkCoproduct : (λ {lu} {ld} → coproductPrim {lu} {ld}) ≡ coproductManual
--   checkCoproduct i {lu} {ld} = coproductPrim {lu} {ld}


--   listPrim : SqFill (List A)
--   listPrim = sqFill (List A)

--   listManual : SqFill (List A)
--   listManual = SqFill.SqFillList.SqFillList A (sqFill A)

--   checkList : (λ {lu} {ld} → listPrim {lu} {ld}) ≡ listManual
--   checkList i {lu} {ld} = listPrim

--   -- maybePrim : SqFill (Maybe A)
--   -- maybePrim = sqFill (Maybe A)

--   -- maybeManual : SqFill (Maybe A)
--   -- maybeManual = SqFill.SqFillMaybe.SqFillMaybe A (sqFill A)

--   -- checkMaybe : (λ {lu} {ld} → maybePrim {lu} {ld}) ≡ maybeManual
--   -- checkMaybe i {lu} {ld} = {!!}
--   -- open import Agda.Builtin.Nat

--   -- NN : Type
--   -- NN = Nat × Nat

--   -- ℤ : Type
--   -- ℤ = Σ NN (λ{(n , m) → (k : Nat) → n + k ≡ m + k})

--   -- evaluate: try it on the projects we listed on TYPES abstract,
--   --   rephrase in our primitives in necessary.
--   -- theoretical: is our system canonical? maybe look into how hcomp for inductive types work.
--   -- propose some venues for submitting this as a paper
--   --

-- module sigma-or-product (A : Type) (B : A → Type) where
--   postulate
--     a : A
--     b : B a
--     C : (f : (a : A) → B a) → Type

--   ty' = Σ ((a : A) → B a) (λ f → C f)

--   -- tm' : ty'
--   -- tm' = ({!!} , {!!})

--   -- sqty' = sqFill ty' {tm'} refl refl refl refl

--   -- testty' : sqty' ≡ refl
--   -- testty' _ _ _ = {! ,!}

--   tyProduct : Type
--   tyProduct = Σ A (λ _ → A)

--   tmProduct : tyProduct
--   tmProduct = (a , a)

--   advProduct : SqFill tyProduct
--   advProduct = sqFill tyProduct

--   sqProduct = advProduct {tmProduct} refl refl refl refl

--   -- testProduct : sqProduct ≡ refl
--   -- testProduct _ _ _ = {!a , a!}

-- -- We implemented Pi, Sigma, Nat, Bool, Unit, PathP.
-- module all-in-one-example where
--   open import Agda.Builtin.Nat
--   open import Agda.Builtin.Bool
--   open import Agda.Builtin.Unit

--   ty : Type
--   ty = (⊤ → Σ Bool (λ{true → ⊤ ; false → 2 ≡ 2}))

--   sqty = sqFill ty {λ _ → false , refl} refl refl refl refl
--   sqty' = sqFill ty {λ _ → true , tt} refl refl refl refl

--   adv : sqty ≡ refl
--   adv _ _ _ _ = false , refl

--   adv' : sqty' ≡ refl
--   adv' _ _ _ _ = true , tt

--   sq : (x : Nat) (p q : x ≡ x) → sqFill Nat (λ i → x) (λ i → x) refl refl ≡ refl
--   sq x p q = {!refl!}
