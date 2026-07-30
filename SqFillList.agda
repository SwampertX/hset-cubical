{-# OPTIONS --cubical=no-glue #-}
open import Helper
open import Agda.Builtin.List
open import SqFillDef

module SqFillList where
  module _ {ℓ} (A : Type ℓ) (sqFillA : SqFill A) where
    open import Agda.Builtin.Product

    private
      nil≠cons : {x : A} {xs : List A} → [] ≡ x ∷ xs → ⊥*
      nil≠cons p = transport (cong isNil p) []
        where
        isNil : List A → Type ℓ
        isNil [] = List A
        isNil (_ ∷ _) = ⊥*

      ListCover : (xs ys : List A) → Type ℓ
      ListCover [] [] = ⊤*
      ListCover [] (_ ∷ _) = ⊥*
      ListCover (_ ∷ _) [] = ⊥*
      ListCover (x ∷ xs) (y ∷ ys) = (x ≡ y) × (ListCover xs ys)

      reflCode : (xs : List A) → ListCover xs xs
      reflCode [] = tt*
      reflCode (x ∷ xs) = refl , reflCode xs

      encode : (xs ys : List A) → xs ≡ ys → ListCover xs ys
      encode xs ys = J (λ ys _ → ListCover xs ys) (reflCode xs)

      encodeRefl : (xs : List A) → encode xs xs refl ≡ reflCode xs
      encodeRefl xs = JRefl (λ ys _ → ListCover xs ys) (reflCode xs)

      decode : (xs ys : List A) → ListCover xs ys → xs ≡ ys
      decode [] [] tt* = refl
      decode (x ∷ xs) (y ∷ ys) (p , c) = cong₂ _∷_ p (decode xs ys c)

      decodeRefl : (xs : List A) → decode xs xs (reflCode xs) ≡ refl
      decodeRefl [] = refl
      decodeRefl (x ∷ xs) = cong (cong₂ _∷_ refl) (decodeRefl xs)

      decodeEncode : (xs ys : List A) (p : xs ≡ ys) → decode xs ys (encode xs ys p) ≡ p
      decodeEncode xs _ = J (λ ys p → decode xs ys (encode xs ys p) ≡ p) (transport (λ i → decode xs xs (encodeRefl xs (~ i)) ≡ refl) (decodeRefl xs))

    SqFillList : SqFill {ℓ = ℓ} (List {a = ℓ} A)
    SqFillList {[]} {[]} l {[]} {[]} r u d i j =
               (hcomp (λ where k (i = i0) → decodeEncode _ _ l k j
                               k (i = i1) → decodeEncode _ _ r k j
                               k (j = i0) → decodeEncode _ _ u k i
                               k (j = i1) → decodeEncode _ _ d k i) [])
    SqFillList {lu ∷ lus} {ld ∷ lds} l {ru ∷ rus} {rd ∷ rds} r u d i j =
               (hcomp (λ where k (i = i0) → decodeEncode (lu ∷ lus) (ld ∷ lds) l k j
                               k (i = i1) → decodeEncode (ru ∷ rus) (rd ∷ rds) r k j
                               k (j = i0) → decodeEncode (lu ∷ lus) (ru ∷ rus) u k i
                               k (j = i1) → decodeEncode (ld ∷ lds) (rd ∷ rds) d k i)
                  (sqFillA (encode _ _ l .fst) (encode _ _ r .fst) (encode _ _ u .fst) (encode _ _ d .fst) i j
                      ∷ SqFillList {lus} (decode _ _ (encode _ _ l .snd))
                                          (decode _ _ (encode _ _ r .snd))
                                          (decode _ _ (encode _ _ u .snd))
                                          (decode _ _ (encode _ _ d .snd)) i j))
    SqFillList {[]} {_ ∷ _} l {_} {_} _ _ _ = ⊥*-elim (nil≠cons l)
    SqFillList {[]} {[]} _ {_ ∷ _} {_} _ u _ = ⊥*-elim (nil≠cons u)
    SqFillList {[]} {[]} _ {[]} {_ ∷ _} _ _ d = ⊥*-elim (nil≠cons d)
    SqFillList {_ ∷ _} {[]} l {_} {_} _ _ _ = ⊥*-elim (nil≠cons (sym l))
    SqFillList {_ ∷ _} {_ ∷ _} _ {[]} {_} _ u _ = ⊥*-elim (nil≠cons (sym u))
    SqFillList {_ ∷ _} {_ ∷ _} _ {_ ∷ _} {[]} _ _ d = ⊥*-elim (nil≠cons (sym d))

  {-# BUILTIN SQFILLLIST SqFillList #-}

    -- -- An experiment with the cover as a list as well. Matches on indexed datatypes, unsupported
    -- module SqFillList' (A : Type) (sqFillA : SqFill A) where
    --   nil≠cons : {x : A} {xs : List A} → [] ≡ x ∷ xs → ⊥
    --   nil≠cons p = transport (cong isNil p) tt
    --       where
    --       isNil : List A → Type
    --       isNil [] = ⊤
    --       isNil (_ ∷ _) = ⊥

    --   data ListCover : List A → List A → Type where
    --     nilListCover : ListCover [] []
    --     consListCover : {x y : A} {xs ys : List A} → x ≡ y → ListCover xs ys → ListCover (x ∷ xs) (y ∷ ys)

    --   reflCode : (xs : List A) → ListCover xs xs
    --   reflCode [] = nilListCover
    --   reflCode (x ∷ xs) = consListCover refl (reflCode xs)

    --   encode : (xs ys : List A) → xs ≡ ys → ListCover xs ys
    --   encode xs ys = J (λ ys _ → ListCover xs ys) (reflCode xs)

    --   -- Warning: unsupported index matching
    --   -- decode : (xs ys : List A) → ListCover xs ys → xs ≡ ys
    --   -- decode [] [] nilListCover = refl
    --   -- decode (x ∷ xs) (y ∷ ys) (consListCover p ps) = cong₂ _∷_ p (decode xs ys ps)
