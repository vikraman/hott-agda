module hott.types.join where

open import hott.core.universe
open import hott.types.span
open import hott.types.product
open import hott.types.pushout

module _ {a b} where

  *-span : (A : Set a) (B : Set b) → span
  *-span A B = mkspan A B (A × B) pr₁ pr₂

  _*_ : (A : Set a) (B : Set b) → Set (suc (a ⊔ b))
  A * B = pushout (*-span A B)
