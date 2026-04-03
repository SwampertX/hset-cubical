{-# OPTIONS --guardedness #-}

module coind-univ where

  postulate A : Set

  -- data D : Set where
  --   cons : (D → A) → D

  record U : Set₁ where
    coinductive
    field
      El : Set
      IdP : (B : U → El) (a0 a1 : El) (a2 : El) → El → El → U
    -- Id : El → El → U
    -- Id A B = IdP
  open U

  open import Agda.Builtin.Sigma


  -- ΣU : (A : U) → (B : El A → U) → U
  -- ΣU A B .El = Σ (El A) (λ a → El (B a))
  -- ΣU A B .Id (a0 , b0) (a1 , b1) = ΣU (Id A a0 a1) (λ a2 → {!Id (B a0) b0 b1!})

  -- ×U : U → U → U
  -- ×U A B .El = Σ (El A) (λ _ → El B)
  -- ×U A B .Id (a0 , b0) (a1 , b1) = ×U (Id A a0 a1) (Id B b0 b1)
