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
  sigmaPrim = sqFill (Σ A (λ a → B a))

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

