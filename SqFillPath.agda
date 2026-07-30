{-# OPTIONS --cubical=no-glue #-}

open import Helper

module SqFillPath where
  module _ {ℓ} (A : Type ℓ) (a b : A) (SqFillA : SqFill A)  where
    SqFillPath : SqFill (a ≡ b)
    SqFillPath {lu} l r u d i j =
        hcomp (λ k → λ {(i = i0) → isPropa≡b lu (l j) k
                      ; (i = i1) → isPropa≡b lu (r j) k
                      ; (j = i0) → isPropa≡b lu (u i) k
                      ; (j = i1) → isPropa≡b lu (d i) k}) lu
        where
        isPropa≡b : (p q : a ≡ b) → p ≡ q
        isPropa≡b p q = SqFillA p q refl refl


  {-# BUILTIN SQFILLPATH SqFillPath #-}
  -- Only one of SqFillA or SqFillB is needed. Currently we request for both an only use SqFillA.
  module _ {ℓ} (A B : Type ℓ) (a : A) (b : B) (P : A ≡ B) (SqFillA : SqFill A) where
    SqFillPathP : SqFill (PathP (λ i → P i) a b)
    SqFillPathP {lu} l r u d i j =
        hcomp (λ k → λ {(i = i0) → isPropa≡b lu (l j) k
                      ; (i = i1) → isPropa≡b lu (r j) k
                      ; (j = i0) → isPropa≡b lu (u i) k
                      ; (j = i1) → isPropa≡b lu (d i) k}) lu
        where
        isPropa≡b : (p q : PathP (λ k → P k) a b) → p ≡ q
        isPropa≡b p q i k =
          comp (λ l → P (k ∧ l))
               (λ l → λ{(k = i0) → a ;
                        (k = i1) → transp (λ j → P (l ∨ (~ j))) l b ;
                        (i = i0) → wallp (~ l) k ;
                        (i = i1) → wallq (~ l) k })
               (SqFillA pa qa (refl {x = a}) (refl {x = transport (sym P) b}) i k)
          where
            pa : a ≡ transport (sym P) b
            pa k = transp (λ l → P ((~ l) ∧ k)) (~ k) (p k)
            qa : a ≡ transport (sym P) b
            qa k = transp (λ l → P ((~ l) ∧ k)) (~ k) (q k)

            wallp : PathP (λ l → PathP (λ k → P (k ∧ ~ l)) a (transp (λ k → P (~ l ∨ ~ k)) (~ l) b)) p pa
            wallp l k = transp (λ j → P (k ∧ ~ (l ∧ j))) (~ (k ∧ l)) (p k)
            wallq : PathP (λ l → PathP (λ k → P (k ∧ ~ l)) a (transp (λ k → P (~ l ∨ ~ k)) (~ l) b)) q qa
            wallq l k = transp (λ j → P (k ∧ ~ (l ∧ j))) (~ (k ∧ l)) (q k)

  {-# BUILTIN SQFILLPATHP SqFillPathP #-}

  -- TODO: can we request for (SqFill A ⊎ SqFill B) and have a term that adjusts?
  --   this then requires the filling to be done symmetrically wrt A and B (not too hard)
  -- module SqFillPathP' (A B : Type) (P : A ≡ B) (SqFillAorB : SqFill A ⊎ SqFill B) where
  --   SqFillPathP : {a : A} {b : B} → SqFill (PathP (λ i → P i) a b)
  --   SqFillPathP {a} {b} {lu} {ld} l r u d i j =
  --       hcomp (λ k → λ {(i = i0) → isPropa≡b lu (l j) k
  --                     ; (i = i1) → isPropa≡b lu (r j) k
  --                     ; (j = i0) → isPropa≡b lu (u i) k
  --                     ; (j = i1) → isPropa≡b lu (d i) k}) lu
  --       where
  --       isPropa≡b : {a : A} {b : B} (p q : PathP (λ k → P k) a b) → p ≡ q
  --       isPropa≡b {a} {b} p q i k =
  --         comp (λ l → P (k ∧ l))
  --              (λ l → λ{(k = i0) → a ;
  --                       (k = i1) → transp (λ j → P (l ∨ (~ j))) l b ;
  --                       (i = i0) → wallp (~ l) k ;
  --                       (i = i1) → wallq (~ l) k })
  --              (SqFillA pa qa (refl {x = a}) (refl {x = transport (sym P) b}) i k)
  --         where
  --           pa : a ≡ transport (sym P) b
  --           pa k = transp (λ l → P ((~ l) ∧ k)) (~ k) (p k)
  --           qa : a ≡ transport (sym P) b
  --           qa k = transp (λ l → P ((~ l) ∧ k)) (~ k) (q k)

  --           wallp : PathP (λ l → PathP (λ k → P (k ∧ ~ l)) a (transp (λ k → P (~ l ∨ ~ k)) (~ l) b)) p pa
  --           wallp l k = transp (λ j → P (k ∧ ~ (l ∧ j))) (~ (k ∧ l)) (p k)
  --           wallq : PathP (λ l → PathP (λ k → P (k ∧ ~ l)) a (transp (λ k → P (~ l ∨ ~ k)) (~ l) b)) q qa
  --           wallq l k = transp (λ j → P (k ∧ ~ (l ∧ j))) (~ (k ∧ l)) (q k)
