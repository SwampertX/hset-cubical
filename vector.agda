open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

module vector where
  data vec (A : Set) : Nat → Set where
    nil : vec A 0
    cons : {n : Nat} → A → vec A n → vec A (suc n)
    weird : {n : Nat} → A → A → vec A (2 * n) → vec A (2 * (suc n))

  -- variable
  --   A : Set

  -- head : {n : Nat} → vec A (suc n) → A
  -- head (cons x _) = x

  -- pred : Nat → Nat
  -- pred 0 = 0
  -- pred (suc n) = n

  -- tail : {n : Nat} → vec A n → vec A (pred n)
  -- tail nil = nil
  -- tail (cons _ xs) = xs

  -- concat : {n m : Nat} → vec A n → vec A m → vec A (n + m)
  -- concat nil ys = ys
  -- concat (cons x xs) ys = cons x (concat xs ys)

  -- concat-nil : {n : Nat} (xs : vec A n) → concat xs nil ≡ xs
