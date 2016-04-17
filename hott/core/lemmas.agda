module hott.core.lemmas where

open import hott.core.universe
open import hott.core.equivalence
open import hott.core.identity

module _ {a} {A : Set a} {x : A} where

  refl∙p≡p : {y : A} → (p : x ≡ y) → refl _ ∙ p ≡ p
  refl∙p≡p (refl _) = refl (refl x)

  p≡refl∙p : {y : A} → (p : x ≡ y) → p ≡ refl _ ∙ p
  p≡refl∙p (refl _) = refl (refl x)

  p∙refl≡p : {y : A} → (p : x ≡ y) → p ∙ refl _ ≡ p
  p∙refl≡p (refl _) = refl (refl x)

  p≡p∙refl : {y : A} → (p : x ≡ y) → p ≡ p ∙ refl _
  p≡p∙refl (refl _) = refl (refl x)

  p⁻¹⁻¹≡p : {y : A} → (p : x ≡ y) → p ⁻¹ ⁻¹ ≡ p
  p⁻¹⁻¹≡p (refl _) = refl (refl x)

  p≡p⁻¹⁻¹ : {y : A} → (p : x ≡ y) → p ≡ p ⁻¹ ⁻¹
  p≡p⁻¹⁻¹ (refl _) = refl (refl x)

  p⁻¹∙p≡refl : {y : A} → (p : x ≡ y) → p ⁻¹ ∙ p ≡ refl _
  p⁻¹∙p≡refl (refl _) = refl (refl x)

  p∙p⁻¹≡refl : {y : A} → (p : x ≡ y) → p ∙ p ⁻¹ ≡ refl _
  p∙p⁻¹≡refl (refl _) = refl (refl x)

  ⁻¹-comm : {y z : A} → (p : x ≡ y) (q : y ≡ z)
          → (p ∙ q) ⁻¹ ≡ q ⁻¹ ∙ p ⁻¹
  ⁻¹-comm (refl _) (refl _) = refl (refl x)

  ∙-assoc : {y z w : A} → (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
          → p ∙ q ∙ r ≡ p ∙ (q ∙ r)
  ∙-assoc (refl _) (refl _) (refl _) = refl (refl x)

module _ {a} {A : Set a} {x : A} where

  ap-id : {y : A} (p : x ≡ y) → ap id p ≡ p
  ap-id (refl _) = refl (refl x)

module _ {a b} {A : Set a} {B : Set b} (f : A → B) {x : A} where

  ap-∙ : {y z : A} (p : x ≡ y) (q : y ≡ z)
       → ap f (p ∙ q) ≡ ap f p ∙ ap f q
  ap-∙ (refl _) (refl _) = refl (refl (f x))

  ap-⁻¹ : {y : A} (p : x ≡ y)
        → ap f (p ⁻¹) ≡ (ap f p) ⁻¹
  ap-⁻¹ (refl _) = refl (refl (f x))

  module _ {c} {C : Set c} (g : B → C) where

    ap-∘ : {y : A} (p : x ≡ y)
         → ap (g ∘ f) p ≡ ap g (ap f p)
    ap-∘ (refl _) = refl (refl (g (f x)))

module _ {a b} {A : Set a} {B : Set b} {x : A} where

  ↓-id : {y : A} (p : x ≡ y) (q : x ≡ x)
       → q ≡ p ⁻¹ ∙ q ∙ p [ (λ x → x ≡ x) ↓ p ]
  ↓-id (refl _) (refl _) = refl (refl x)

  ↓-ap : {y : A} (f g : A → B) (p : x ≡ y) (q : f x ≡ g x)
       → q ≡ ap f p ⁻¹ ∙ q ∙ ap g p [ (λ x → f x ≡ g x) ↓ p ]
  ↓-ap f g (refl _) q =
    begin
      q
    ≡⟨ p≡p∙refl q ⟩
      q ∙ refl (g x)
    ≡⟨ ap (λ p → p ∙ refl (g x)) (p≡refl∙p q) ⟩
      refl _ ∙ q ∙ refl _
    ∎
