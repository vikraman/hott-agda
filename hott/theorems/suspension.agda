{-# OPTIONS --without-K --rewriting #-}

module hott.theorems.suspension where

open import hott.core
open import hott.types

{-# REWRITE βrec-∑-merid #-}
{-# REWRITE βind-∑-merid #-}
{-# REWRITE β-rec-pushout-glue #-}
{-# REWRITE β-ind-pushout-glue #-}

module _ {a} {A : Set a} where

  module ∑A≃bool*A where

    f : ∑ A → bool * A
    f = rec-∑ (bool * A) (inl false) (inl true)
              (λ a → glue (false , a) ∙ glue (true , a) ⁻¹)

    g : bool * A → ∑ A
    g = rec-pushout (∑ A) g-bool g-A g-glue
      where g-bool : bool → ∑ A
            g-bool true = 𝑆 {A = A}
            g-bool false = 𝑁 {A = A}

            g-A : A → ∑ A
            g-A _ = 𝑆

            g-glue : (s : bool × A) → g-bool (pr₁ s) ≡ 𝑆
            g-glue (true , a) = refl 𝑆
            g-glue (false , a) = merid a

    f-g-inl : (b : bool) → f (g (inl b)) ≡ inl b
    f-g-inl true = refl (inl true)
    f-g-inl false = refl (inl false)

    f-g-inr : (a : A) → f (g (inr a)) ≡ inr a
    f-g-inr a = glue (true , a)

    f-g-glue : (c : bool × A) → f-g-inl (pr₁ c) ≡ glue (true , pr₂ c) [ (λ x → f (g x) ≡ x) ↓ glue c ]
    f-g-glue (true  , a) =
      begin
        transport (λ x → f (g x) ≡ x) (glue (true , a)) (refl (f (g (inl true))))
      ≡⟨ ↓-ap (f ∘ g) id (glue (true , a)) (refl (inl true)) ⟩
        ap (f ∘ g) (glue (true , a)) ⁻¹ ∙ refl (inl true) ∙ ap id (glue (true , a))
      ≡⟨ ap (λ p → ap (f ∘ g) (glue (true , a)) ⁻¹ ∙ refl (inl true) ∙ p) (ap-id (glue (true , a))) ⟩
        ap (f ∘ g) (glue (true , a)) ⁻¹ ∙ refl (inl true) ∙ glue (true , a)
      ≡⟨ ap (λ p → p ∙ glue (true , a)) (p∙refl≡p (ap (f ∘ g) (glue (true , a)) ⁻¹)) ⟩
        ap (f ∘ g) (glue (true , a)) ⁻¹ ∙ glue (true , a)
      ≡⟨ ap (λ p → p ⁻¹ ∙ glue (true , a)) (ap-∘ g f (glue (true , a))) ⟩
        ap f (ap g (glue (true , a))) ⁻¹ ∙ glue (true , a)
      ≡⟨ ap (λ p → ap f p ⁻¹ ∙ glue (true , a)) (refl (refl 𝑆)) ⟩
        ap f (refl 𝑆) ⁻¹ ∙ glue (true , a)
      ≡⟨ ap (λ p → p ⁻¹ ∙ glue (true , a)) (refl (refl (inl true))) ⟩
        refl (inl true) ⁻¹ ∙ glue (true , a)
      ≡⟨ ap (λ p → p ∙ glue (true , a)) (refl (refl (inl true))) ⟩
        refl (inl true) ∙ glue (true , a)
      ≡⟨ refl∙p≡p (glue (true , a)) ⟩
        glue (true , a)
      ∎
    f-g-glue (false , a) =
      begin
        transport (λ x → f (g x) ≡ x) (glue (false , a)) (refl (f (g (inl false))))
      ≡⟨ ↓-ap (f ∘ g) id (glue (false , a)) (refl (inl false)) ⟩
        ap (f ∘ g) (glue (false , a)) ⁻¹ ∙ refl ( (inl false)) ∙ ap id (glue (false , a))
      ≡⟨ ap (λ p → ap (f ∘ g) (glue (false , a)) ⁻¹ ∙ refl (inl false) ∙ p) (ap-id (glue (false , a))) ⟩
        ap (f ∘ g) (glue (false , a)) ⁻¹ ∙ refl (inl false) ∙ glue (false , a)
      ≡⟨ ap (λ p → p ∙ glue (false , a)) (p∙refl≡p (ap (f ∘ g) (glue (false , a)) ⁻¹)) ⟩
        ap (f ∘ g) (glue (false , a)) ⁻¹ ∙ glue (false , a)
      ≡⟨ ap (λ p → p ⁻¹ ∙ glue (false , a)) (ap-∘ g f (glue (false , a))) ⟩
        ap f (ap g (glue (false , a))) ⁻¹ ∙ glue (false , a)
      ≡⟨ ap (λ p → ap f p ⁻¹ ∙ glue (false , a)) (refl (merid a)) ⟩
        ap f (merid a) ⁻¹ ∙ glue (false , a)
      ≡⟨ ap (λ p → p ∙ glue (false , a)) (refl ((glue (false , a) ∙ glue (true , a) ⁻¹) ⁻¹)) ⟩
        (glue (false , a) ∙ glue (true , a) ⁻¹) ⁻¹ ∙ glue (false , a)
      ≡⟨ ap (λ p → p ∙ glue (false , a)) (⁻¹-comm (glue (false , a)) (glue (true , a) ⁻¹)) ⟩
        glue (true , a) ⁻¹ ⁻¹ ∙ glue (false , a) ⁻¹ ∙ glue (false , a)
      ≡⟨ ap (λ p → p ∙ glue (false , a) ⁻¹ ∙ glue (false , a)) (p⁻¹⁻¹≡p (glue (true , a))) ⟩
        glue (true , a) ∙ glue (false , a) ⁻¹ ∙ glue (false , a)
      ≡⟨ ∙-assoc (glue (true , a)) (glue (false , a) ⁻¹) (glue (false , a)) ⟩
        glue (true , a) ∙ (glue (false , a) ⁻¹ ∙ glue (false , a))
      ≡⟨ ap (λ p → glue (true , a) ∙ p) (p⁻¹∙p≡refl (glue (false , a))) ⟩
        glue (true , a) ∙ refl (inr a)
      ≡⟨ p∙refl≡p (glue (true , a)) ⟩
        glue (true , a)
      ∎

    f-g : f ∘ g ~ id
    f-g = ind-pushout (λ x → f (g x) ≡ x) f-g-inl f-g-inr f-g-glue

    g-f-merid : ∀ a → refl (g (f 𝑁)) ≡ refl (g (f 𝑆)) [ (λ x → g (f x) ≡ x) ↓ merid a ]
    g-f-merid a =
      begin
        transport (λ x → g (f x) ≡ x) (merid a) (refl (g (f 𝑁)))
      ≡⟨ ↓-ap (g ∘ f) id (merid a) (refl 𝑁) ⟩
        ap (g ∘ f) (merid a) ⁻¹ ∙ refl 𝑁 ∙ ap id (merid a)
      ≡⟨ ap (λ p → ap (g ∘ f) (merid a) ⁻¹ ∙ refl 𝑁 ∙ p) (ap-id (merid a)) ⟩
        ap (g ∘ f) (merid a) ⁻¹ ∙ refl 𝑁 ∙ merid a
      ≡⟨ ap (λ p → p ∙ merid a) (p∙refl≡p (ap (g ∘ f) (merid a) ⁻¹)) ⟩
        ap (g ∘ f) (merid a) ⁻¹ ∙ merid a
      ≡⟨ ap (λ p → p ⁻¹ ∙ merid a) (ap-∘ f g (merid a)) ⟩
        ap g (ap f (merid a)) ⁻¹ ∙ merid a
      ≡⟨ ap (λ p → ap g p ⁻¹ ∙ merid a) (refl (glue (false , a) ∙ glue (true , a) ⁻¹)) ⟩
        ap g (glue (false , a) ∙ glue (true , a) ⁻¹) ⁻¹ ∙ merid a
      ≡⟨ ap (λ p → p ⁻¹ ∙ merid a) (ap-∙ g (glue (false , a)) (glue (true , a) ⁻¹)) ⟩
        (ap g (glue (false , a)) ∙ ap g (glue (true , a) ⁻¹)) ⁻¹ ∙ merid a
      ≡⟨ ap (λ p → (p ∙ ap g (glue (true , a) ⁻¹)) ⁻¹ ∙ merid a) (refl (merid a)) ⟩
        (merid a ∙ ap g (glue (true , a) ⁻¹)) ⁻¹ ∙ merid a
      ≡⟨ ap (λ p → (merid a ∙ p) ⁻¹ ∙ merid a) (ap-⁻¹ g (glue (true , a))) ⟩
        (merid a ∙ ap g (glue (true , a)) ⁻¹) ⁻¹ ∙ merid a
      ≡⟨ ap (λ p → (merid a ∙ p ⁻¹) ⁻¹ ∙ merid a) (refl (refl (g (inl true)))) ⟩
        (merid a ∙ refl 𝑆 ⁻¹) ⁻¹ ∙ merid a
      ≡⟨ ap (λ p → (merid a ∙ p) ⁻¹ ∙ merid a) (refl (refl 𝑆 ⁻¹)) ⟩
        (merid a ∙ refl 𝑆) ⁻¹ ∙ merid a
      ≡⟨ ap (λ p → p ⁻¹ ∙ merid a) (p∙refl≡p (merid a)) ⟩
        merid a ⁻¹ ∙ merid a
      ≡⟨ p⁻¹∙p≡refl (merid a) ⟩
        refl 𝑆
      ∎

    g-f : g ∘ f ~ id
    g-f = ind-∑ (λ x → g (f x) ≡ x) (refl (g (f 𝑁))) (refl (g (f 𝑆))) g-f-merid

  ∑A≃bool*A : ∑ A ≃ bool * A
  ∑A≃bool*A = let open ∑A≃bool*A in
    f , record { g = g
               ; f-g = f-g
               ; g-f = g-f
               }

  ∑A≡bool*A : ∑ A ≡ bool * A
  ∑A≡bool*A with ua
  ... | _ , eq = is-equiv.g eq ∑A≃bool*A

  bool*A≡∑A : bool * A ≡ ∑ A
  bool*A≡∑A = ∑A≡bool*A ⁻¹
