{-# OPTIONS --cubical=no-glue #-}

open import Helper
open import Agda.Builtin.Coproduct renaming (_⊎_ to _+_)

module SqFillCoproduct where
  module _ {ℓ ℓ'} (A : Type ℓ) (SqFillA : SqFill A) (B : Type ℓ') (SqFillB : SqFill B) where
    private
      inl≠inr : (x : A) (y : B) → (inl x ≡ inr y) → ⊥*
      inl≠inr x y p = transport (cong isLeft p) tt*
        where
          isLeft : (A + B) → Type (ℓ ⊔ ℓ')
          isLeft (inl x) = ⊤*
          isLeft (inr y) = ⊥*

      Cover : (c c' : A + B) → Type (ℓ ⊔ ℓ')
      Cover (inl x) (inl y) = Lift (ℓ ⊔ ℓ') (x ≡ y)
      Cover (inl _) (inr _) = ⊥*
      Cover (inr _) (inl _) = ⊥*
      Cover (inr x) (inr y) = Lift (ℓ ⊔ ℓ') (x ≡ y)

      reflCode : (c : A + B) → Cover c c
      reflCode (inl x) = lift refl
      reflCode (inr x) = lift refl

      encode : {c c' : A + B} → c ≡ c' → Cover c c'
      encode {c = c} p = transport (λ i → Cover c (p i)) (reflCode c)

      decode : {c c' : A + B} → Cover c c' → (c ≡ c')
      decode {c = inl x} {c' = inl y} (lift p) = cong inl p
      decode {c = inr x} {c' = inr y} (lift p) = cong inr p

      decodeEncode : {c c' : A + B} (p : c ≡ c') → decode (encode p) ≡ p
      decodeEncode {c = inl x} = J (λ c' p → decode (encode p) ≡ p) (cong (cong inl) (transportRefl refl))
      decodeEncode {c = inr x} = J (λ c' p → decode (encode p) ≡ p) (cong (cong inr) (transportRefl refl))

    SqFillCoproduct : SqFill (A + B)
    SqFillCoproduct {inl lu} {inl ld} l {inl ru} {inl rd} r u d i j =
        (hcomp (λ where
            k (i = i0) → decodeEncode l k j
            k (i = i1) → decodeEncode r k j
            k (j = i0) → decodeEncode u k i
            k (j = i1) → decodeEncode d k i)
        (inl {A = A} {B = B} (SqFillA (encode l .Lift.lower) (encode r .Lift.lower) (encode u .Lift.lower) (encode d .Lift.lower) i j)))
    SqFillCoproduct {inr lu} {inr ld} l {inr ru} {inr rd} r u d i j =
        (hcomp (λ where
            k (i = i0) → decodeEncode l k j
            k (i = i1) → decodeEncode r k j
            k (j = i0) → decodeEncode u k i
            k (j = i1) → decodeEncode d k i)
        (inr {A = A} {B = B} (SqFillB (encode l .Lift.lower) (encode r .Lift.lower) (encode u .Lift.lower) (encode d .Lift.lower) i j)))
    SqFillCoproduct {inl x} {inr y} l _ _ _                 = ⊥*-elim (inl≠inr x y l)
    SqFillCoproduct {inl x} {inl _} _ {inr y} _ u _         = ⊥*-elim (inl≠inr x y u)
    SqFillCoproduct {inl _} {inl x} _ {inl _} {inr y} _ _ d = ⊥*-elim (inl≠inr x y d)
    SqFillCoproduct {inr x} {inl y} l _ _ _                 = ⊥*-elim (inl≠inr y x (sym l))
    SqFillCoproduct {inr x} {inr _} _ {inl y} _ u _         = ⊥*-elim (inl≠inr y x (sym u))
    SqFillCoproduct {inr _} {inr x} _ {inr _} {inl y} _ _ d = ⊥*-elim (inl≠inr y x (sym d))

  {-# BUILTIN SQFILLCOPRODUCT SqFillCoproduct #-}
