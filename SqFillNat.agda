{-# OPTIONS --cubical=no-glue #-}

open import Helper
open import Agda.Builtin.Nat

module SqFillNat where
  private
    zero≠suc : {n : Nat} → zero ≡ suc n → ⊥
    zero≠suc p = transport (cong isZero p) zero
        where
        isZero : Nat → Type
        isZero zero = Nat
        isZero (suc _) = ⊥

    NatCover : (n n' : Nat) → Type
    NatCover zero zero = ⊤
    NatCover (suc n) (suc n') = NatCover n n'
    NatCover _ _ = ⊥

    reflCode : (n : Nat) → NatCover n n
    reflCode zero = tt
    reflCode (suc n) = reflCode n

    encode : (n n' : Nat) → n ≡ n' → NatCover n n'
    encode n n' = J (λ n' _ → NatCover n n') (reflCode n)

    decode : (n n' : Nat) → NatCover n n' → n ≡ n'
    decode zero zero tt = refl
    decode (suc n) (suc n') c = cong suc (decode n n' c)

    encodeDecode : (n n' : Nat) (c : NatCover n n') → encode n n' (decode n n' c) ≡ c
    encodeDecode zero zero c = refl
    encodeDecode (suc n) (suc n') c = encodeDecode n n' c

    decodeEncode : (n n' : Nat) (p : n ≡ n') → decode n n' (encode n n' p) ≡ p
    decodeEncode zero n' = J (λ n' p → decode zero n' (encode zero n' p) ≡ p) refl
    decodeEncode (suc n) n' = J (λ n' p → decode (suc n) n' (encode (suc n) n' p) ≡ p) (cong (cong suc) (decodeEncode n n refl))


  SqFillNat : SqFill Nat
  SqFillNat {zero} {zero} l {zero} {zero} r u d i j =
    (hcomp (λ where k (i = i0) → decodeEncode _ _ l k j
                    k (i = i1) → decodeEncode _ _ r k j
                    k (j = i0) → decodeEncode _ _ u k i
                    k (j = i1) → decodeEncode _ _ d k i) zero)
  SqFillNat {suc lu} {suc ld} l {suc ru} {suc rd} r u d i j =
    (hcomp (λ where k (i = i0) → decodeEncode (suc lu) (suc ld) l k j
                    k (i = i1) → decodeEncode (suc ru) (suc rd) r k j
                    k (j = i0) → decodeEncode (suc lu) (suc ru) u k i
                    k (j = i1) → decodeEncode (suc ld) (suc rd) d k i) (
          suc (SqFillNat {lu} (decode lu ld (encode _ _ l))
                              (decode ru rd (encode _ _ r))
                              (decode lu ru (encode _ _ u))
                              (decode ld rd (encode _ _ d)) i j)))
  SqFillNat {zero} {suc _} l {_} {_} _ _ _ = ⊥-elim (zero≠suc l)
  SqFillNat {zero} {zero} _ {suc _} {_} _ u _ = ⊥-elim (zero≠suc u)
  SqFillNat {zero} {zero} _ {zero} {suc _} _ _ d = ⊥-elim (zero≠suc d)
  SqFillNat {suc _} {zero} l {_} {_} _ _ _ = ⊥-elim (zero≠suc (sym l))
  SqFillNat {suc _} {suc _} _ {zero} {_} _ u _ = ⊥-elim (zero≠suc (sym u))
  SqFillNat {suc _} {suc _} _ {suc _} {zero} _ _ d = ⊥-elim (zero≠suc (sym d))

  {-# BUILTIN SQFILLNAT SqFillNat #-}
