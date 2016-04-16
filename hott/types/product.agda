module hott.types.product where

open import hott.core.universe

record _×_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    pr₁ : A
    pr₂ : B

open _×_ public
