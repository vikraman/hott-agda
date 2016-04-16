module hott.types.hspace where

open import hott.core.identity

record hspace {a} (A : Set a) : Set a where
  field
    e : A
    μ : A → A → A
    μea : (a : A) → μ e a ≡ a
    μae : (a : A) → μ a e ≡ a
