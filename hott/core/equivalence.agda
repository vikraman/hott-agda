module hott.core.equivalence where

open import hott.core.universe
open import hott.core.identity

module _ {a b c} {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} where

  infixr 9 _∘_

  _∘_ : (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) → ((x : A) → C (g x))
  f ∘ g = λ x → f (g x)

module _ {a b} {A : Set a} {B : A → Set b} where

  infixr 8 _~_

  _~_ : (f g : (x : A) → B x) → Set (a ⊔ b)
  f ~ g = (x : A) → f x ≡ g x

module _ {a} {A : Set a} where

  id : A → A
  id a = a

module _ {a b} {A : Set a} {B : Set b} where

  record is-equiv (f : A → B) : Set (a ⊔ b) where
    field
      g : B → A
      f-g : f ∘ g ~ id
      g-f : g ∘ f ~ id
      -- adj : (a : A) → ap f (g-f a) ≡ f-g (f a)

open import hott.types.sigma

infixr 7 _≃_

_≃_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A ≃ B = Σ (A → B) is-equiv
