{-# OPTIONS --cubical=full #-}

open import Cubical.Foundations.Prelude

-- what is a if-then-else-end definition such that [if _ then i else i end] equals i definitionally?
--
if_then_else_end : I → I → I → I
-- if k then i else j end = ((~ k) ∧ j) ∨ (k ∧ i)
-- if k then i else j end = (j ∨ ~ k) ∧ (i ∨ k)
if i then j else k end = (k ∧ ~ i) ∨ ((i ∨ k) ∧ j)
