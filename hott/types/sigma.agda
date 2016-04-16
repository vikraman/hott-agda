module hott.types.sigma where

open import hott.core.universe

infixr 4 _,_

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    pr₁ : A
    pr₂ : B pr₁

open Σ public
