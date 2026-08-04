{-# OPTIONS --cubical=no-glue #-}

open import Helper
open import Agda.Builtin.Maybe
open import SqFillDef

module SqFillMaybe where
  module _ {ℓ} (A : Type ℓ) (sqFillA : SqFill A) where
    open import Agda.Builtin.Unit

    private
      nothing≠just : {x : A} → (nothing ≡ just x) → ⊥
      nothing≠just p = transport (cong isNothing p) tt
          where
          isNothing : Maybe A → Type
          isNothing nothing = ⊤
          isNothing (just y) = ⊥

      MaybeCover : (c c' : Maybe A) → Type ℓ
      MaybeCover nothing nothing   = ⊤*
      MaybeCover nothing (just _)  = ⊥*
      MaybeCover (just x) (just y) = x ≡ y
      MaybeCover (just _) nothing  = ⊥*

      reflCode : (c : Maybe A) → MaybeCover c c
      reflCode nothing = tt*
      reflCode (just x) = refl

      encode : {c c' : Maybe A} → c ≡ c' → MaybeCover c c'
      encode {c = c} p = transport (λ i → MaybeCover c (p i)) (reflCode c)

      decode : {c c' : Maybe A} → MaybeCover c c' → c ≡ c'
      decode {c = nothing} {c' = nothing} _ = refl
      decode {c = just x} {c' = just y} = cong just

      decodeEncode : {c c' : Maybe A} (p : c ≡ c') → decode (encode p) ≡ p
      decodeEncode {c = nothing} = J (λ c' p → decode (encode p) ≡ p) refl
      decodeEncode {c = just x} = J (λ c' p → decode (encode p) ≡ p) (cong (cong just) (transportRefl refl))

    SqFillMaybe : SqFill (Maybe A)
    SqFillMaybe {nothing} {nothing} l {nothing} {nothing} r u d i j =
        (hcomp (λ where
            k (i = i0) → decodeEncode l k j
            k (i = i1) → decodeEncode r k j
            k (j = i0) → decodeEncode u k i
            k (j = i1) → decodeEncode d k i) nothing)
    SqFillMaybe {just lu} {just ld} l {just ru} {just rd} r u d i j =
        (hcomp (λ where
            k (i = i0) → decodeEncode l k j
            k (i = i1) → decodeEncode r k j
            k (j = i0) → decodeEncode u k i
            k (j = i1) → decodeEncode d k i)
        (just (sqFillA (encode l) (encode r) (encode u) (encode d) i j)))
    SqFillMaybe {nothing} {just y} l _ _ _                     = ⊥-elim (nothing≠just l)
    SqFillMaybe {nothing} {nothing} _ {just y} _ u _           = ⊥-elim (nothing≠just u)
    SqFillMaybe {nothing} {nothing} _ {nothing} {just y} _ _ d = ⊥-elim (nothing≠just d)
    SqFillMaybe {just x} {nothing} l _ _ _                     = ⊥-elim (nothing≠just (sym l))
    SqFillMaybe {just x} {just _} _ {nothing} _ u _            = ⊥-elim (nothing≠just (sym u))
    SqFillMaybe {just _} {just x} _ {just _} {nothing} _ _ d   = ⊥-elim (nothing≠just (sym d))

  {-# BUILTIN SQFILLMAYBE SqFillMaybe #-}
