module hott.types.product where

open import hott.core.universe
open import hott.types.sigma public

module _ {a b} where

  infixr 2 _×_

  _×_ : (A : Set a) (B : Set b) → Set (a ⊔ b)
  A × B = Σ A (λ _ → B)
