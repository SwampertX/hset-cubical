{-# OPTIONS --cubical=no-glue #-}

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
open import Agda.Builtin.Coproduct
open import Agda.Builtin.Product
open import Helper using (refl)
open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit

data U : Type

El : U → Type

data U where
  Bool' : U
  Pi : (A : U) → (El A → U) → U
  Σ' : (A : U) → (El A → U) → U
  PathP' : (A : I → U) → El (A i0) → El (A i1) → U
  _⊎'_ : U → U → U
  _×'_ : U → U → U
  Nat' : U
  ⊤' : U
  List' : U → U
  Maybe' : U → U


El Bool' =  Bool
El (Pi A B) = (a : El A) → El (B a)
El (Σ' A B) = Σ (El A) (λ a → El (B a))
El (PathP' A a0 a1) = PathP (λ i → El (A i)) a0 a1
El (A ⊎' B) = El A ⊎ El B
El (A ×' B) = El A × El B
El Nat' = Nat
El ⊤' = ⊤
El (List' A) = List (El A)
El (Maybe' A) = Maybe (El A)

open import SqFill

SqFillU : SqFill U
SqFillU {Bool'} {Bool'} l {Bool'} {Bool'} r u d = {!!}
SqFillU {Bool'} {Bool'} l {Bool'} {Pi rd x} r u d = {!!}
SqFillU {Bool'} {Bool'} l {Bool'} {Σ' rd x} r u d = {!!}
SqFillU {Bool'} {Bool'} l {Bool'} {PathP' A x x₁} r u d = {!!}
SqFillU {Bool'} {Bool'} l {Bool'} {rd ⊎' rd₁} r u d = {!!}
SqFillU {Bool'} {Bool'} l {Bool'} {rd ×' rd₁} r u d = {!!}
SqFillU {Bool'} {Bool'} l {Bool'} {Nat'} r u d = {!!}
SqFillU {Bool'} {Bool'} l {Bool'} {⊤'} r u d = {!!}
SqFillU {Bool'} {Bool'} l {Bool'} {List' rd} r u d = {!!}
SqFillU {Bool'} {Bool'} l {Bool'} {Maybe' rd} r u d = {!!}
SqFillU {Bool'} {Bool'} l {Pi ru x} {rd} r u d = {!!}
SqFillU {Bool'} {Bool'} l {Σ' ru x} {rd} r u d = {!!}
SqFillU {Bool'} {Bool'} l {PathP' A x x₁} {rd} r u d = {!!}
SqFillU {Bool'} {Bool'} l {ru ⊎' ru₁} {rd} r u d = {!!}
SqFillU {Bool'} {Bool'} l {ru ×' ru₁} {rd} r u d = {!!}
SqFillU {Bool'} {Bool'} l {Nat'} {rd} r u d = {!!}
SqFillU {Bool'} {Bool'} l {⊤'} {rd} r u d = {!!}
SqFillU {Bool'} {Bool'} l {List' ru} {rd} r u d = {!!}
SqFillU {Bool'} {Bool'} l {Maybe' ru} {rd} r u d = {!!}
SqFillU {Bool'} {Pi ld x} l r u d = {!!}
SqFillU {Bool'} {Σ' ld x} l r u d = {!!}
SqFillU {Bool'} {PathP' A x x₁} l r u d = {!!}
SqFillU {Bool'} {ld ⊎' ld₁} l r u d = {!!}
SqFillU {Bool'} {ld ×' ld₁} l r u d = {!!}
SqFillU {Bool'} {Nat'} l r u d = {!!}
SqFillU {Bool'} {⊤'} l r u d = {!!}
SqFillU {Bool'} {List' ld} l r u d = {!!}
SqFillU {Bool'} {Maybe' ld} l r u d = {!!}
SqFillU {Pi lu x} {ld} l r u d = {!!}
SqFillU {Σ' lu x} {ld} l r u d = {!!}
SqFillU {PathP' A x x₁} {ld} l r u d = {!!}
SqFillU {lu ⊎' lu₁} {ld} l r u d = {!!}
SqFillU {lu ×' lu₁} {ld} l r u d = {!!}
SqFillU {Nat'} {ld} l r u d = {!!}
SqFillU {⊤'} {ld} l r u d = {!!}
SqFillU {List' lu} {ld} l r u d = {!!}
SqFillU {Maybe' lu} {ld} l r u d = {!!}
