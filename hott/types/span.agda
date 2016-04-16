module hott.types.span where

open import hott.core.universe

record span {a b c} : Set (suc (a ⊔ b ⊔ c)) where
  constructor mkspan
  field
    A : Set a
    B : Set b
    C : Set c
    f : C → A
    g : C → B
