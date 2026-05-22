
data U : Set₁ where
  k : Set → U
  -- t : (t : T) → U T
  pi : (A : Set) → (B : A → U) → U

reflect : U → Set
reflect (k x) = x
reflect (pi A B) = (a : A) → reflect (B a)
