module hott.core.lemmas where

open import hott.core.universe
open import hott.core.equivalence
open import hott.core.identity

module _ {a} {A : Set a} {x : A} where

  refl∙p≡p : {y : A} → (p : x ≡ y) → refl ∙ p ≡ p
  refl∙p≡p refl = refl

  p≡refl∙p : {y : A} → (p : x ≡ y) → p ≡ refl ∙ p
  p≡refl∙p refl = refl

  p∙refl≡p : {y : A} → (p : x ≡ y) → p ∙ refl ≡ p
  p∙refl≡p refl = refl

  p≡p∙refl : {y : A} → (p : x ≡ y) → p ≡ p ∙ refl
  p≡p∙refl refl = refl

  p⁻¹⁻¹≡p : {y : A} → (p : x ≡ y) → p ⁻¹ ⁻¹ ≡ p
  p⁻¹⁻¹≡p refl = refl

  p≡p⁻¹⁻¹ : {y : A} → (p : x ≡ y) → p ≡ p ⁻¹ ⁻¹
  p≡p⁻¹⁻¹ refl = refl

  p⁻¹∙p≡refl : {y : A} → (p : x ≡ y) → p ⁻¹ ∙ p ≡ refl
  p⁻¹∙p≡refl refl = refl

  p∙p⁻¹≡refl : {y : A} → (p : x ≡ y) → p ∙ p ⁻¹ ≡ refl
  p∙p⁻¹≡refl refl = refl

  ⁻¹-comm : {y z : A} → (p : x ≡ y) (q : y ≡ z)
          → (p ∙ q) ⁻¹ ≡ q ⁻¹ ∙ p ⁻¹
  ⁻¹-comm refl refl = refl

  ∙-assoc : {y z w : A} → (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
          → p ∙ q ∙ r ≡ p ∙ (q ∙ r)
  ∙-assoc refl refl refl = refl

module _ {a} {A : Set a} {x : A} where

  ap-id : {y : A} (p : x ≡ y) → ap id p ≡ p
  ap-id refl = refl

module _ {a b} {A : Set a} {B : Set b} (f : A → B) {x : A} where

  ap-∙ : {y z : A} (p : x ≡ y) (q : y ≡ z)
       → ap f (p ∙ q) ≡ ap f p ∙ ap f q
  ap-∙ refl refl = refl

  ap-⁻¹ : {y : A} (p : x ≡ y)
        → ap f (p ⁻¹) ≡ (ap f p) ⁻¹
  ap-⁻¹ refl = refl

  module _ {c} {C : Set c} (g : B → C) where

    ap-∘ : {y : A} (p : x ≡ y)
         → ap (g ∘ f) p ≡ ap g (ap f p)
    ap-∘ refl = refl

module _ {a b} {A : Set a} {B : Set b} {x : A} where

  ↓-id : {y : A} (p : x ≡ y) (q : x ≡ x)
       → q ≡ p ⁻¹ ∙ q ∙ p [ (λ x → x ≡ x) ↓ p ]
  ↓-id refl refl = refl

  ↓-ap : {y : A} (f g : A → B) (p : x ≡ y) (q : f x ≡ g x)
       → q ≡ ap f p ⁻¹ ∙ q ∙ ap g p [ (λ x → f x ≡ g x) ↓ p ]
  ↓-ap f g refl q =
    begin
      q
    ≡⟨ p≡p∙refl q ⟩
      q ∙ refl
    ≡⟨ ap (λ p → p ∙ refl) (p≡refl∙p q) ⟩
      refl ∙ q ∙ refl
    ∎
