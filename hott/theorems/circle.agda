{-# OPTIONS --without-K --rewriting #-}

module hott.theorems.circle where

open import hott.core
open import hott.types

{-# REWRITE βrec-S¹-loop #-}
{-# REWRITE βind-S¹-loop #-}
{-# REWRITE βrec-∑-merid #-}
{-# REWRITE βind-∑-merid #-}

module ∑bool≃S¹ where

  f : ∑ bool → S¹
  f = rec-∑ S¹ base base λ { true → loop ; false → refl base }

  g : S¹ → ∑ bool
  g = rec-S¹ (∑ bool) 𝑁 (merid true ∙ (merid false ⁻¹))

  g-f-tr-true : refl 𝑁 ≡ merid false [ (λ b → (g ∘ f) b ≡ b) ↓ merid true ]
  g-f-tr-true =
    begin
      transport (λ b → (g ∘ f) b ≡ b) (merid true) (refl 𝑁)
    ≡⟨ ↓-ap (g ∘ f) id (merid true) (refl 𝑁) ⟩
      ap (g ∘ f) (merid true) ⁻¹ ∙ refl 𝑁 ∙ ap id (merid true)
    ≡⟨ ap (λ p → ap (g ∘ f) (merid true) ⁻¹ ∙ refl 𝑁 ∙ p) (ap-id (merid true)) ⟩
      ap (g ∘ f) (merid true) ⁻¹ ∙ refl 𝑁 ∙ merid true
    ≡⟨ ∙-assoc (ap (g ∘ f) (merid true) ⁻¹) (refl 𝑁) (merid true) ⟩
      ap (g ∘ f) (merid true) ⁻¹ ∙ (refl 𝑁 ∙ merid true)
    ≡⟨ ap (λ p → ap (g ∘ f) (merid true) ⁻¹ ∙ p) (refl∙p≡p (merid true)) ⟩
      ap (g ∘ f) (merid true) ⁻¹ ∙ merid true
    ≡⟨ ap (λ p → p ⁻¹ ∙ merid true) (ap-∘ f g (merid true)) ⟩
      (merid true ∙ merid false ⁻¹) ⁻¹ ∙ merid true
    ≡⟨ ap (λ p → p ∙ merid true) (⁻¹-comm (merid true) (merid false ⁻¹)) ⟩
      merid false ⁻¹ ⁻¹ ∙ merid true ⁻¹ ∙ merid true
    ≡⟨ ∙-assoc (merid false ⁻¹ ⁻¹) (merid true ⁻¹) (merid true) ⟩
      merid false ⁻¹ ⁻¹ ∙ (merid true ⁻¹ ∙ merid true)
    ≡⟨ ap (λ p → merid false ⁻¹ ⁻¹ ∙ p) (p⁻¹∙p≡refl (merid true)) ⟩
      merid false ⁻¹ ⁻¹ ∙ refl 𝑆
    ≡⟨ ap (λ p → p ∙ refl 𝑆) (p⁻¹⁻¹≡p (merid false)) ⟩
      merid false ∙ refl 𝑆
    ≡⟨ p∙refl≡p (merid false) ⟩
      merid false
    ∎

  g-f-tr-false : refl 𝑁 ≡ merid false [ (λ b → (g ∘ f) b ≡ b) ↓ merid false ]
  g-f-tr-false =
    begin
      transport (λ b → (g ∘ f) b ≡ b) (merid false) (refl  𝑁)
    ≡⟨ ↓-ap (g ∘ f) id (merid false) (refl 𝑁) ⟩
      ap (g ∘ f) (merid false) ⁻¹ ∙ refl  𝑁 ∙ ap id (merid false)
    ≡⟨ ap (λ p → ap (g ∘ f) (merid false) ⁻¹ ∙ refl  𝑁 ∙ p) (ap-id (merid false)) ⟩
      ap (g ∘ f) (merid false) ⁻¹ ∙ refl  𝑁 ∙ merid false
    ≡⟨ ap (λ p → p ∙ merid false) (p∙refl≡p (ap (g ∘ f) (merid false) ⁻¹)) ⟩
      ap (g ∘ f) (merid false) ⁻¹ ∙ merid false
    ≡⟨ ap (λ p → p ⁻¹ ∙ merid false) (ap-∘ f g (merid false)) ⟩
      ap g (ap f (merid false)) ⁻¹ ∙ merid false
    ≡⟨ refl∙p≡p (merid false) ⟩
      merid false
    ∎

  g-f : g ∘ f ~ id
  g-f = ind-∑ (λ x → g (f x) ≡ x) (refl (g (f 𝑁))) (merid false)
             λ { true → g-f-tr-true ; false → g-f-tr-false }

  f-g-loop : ap (f ∘ g) loop ≡ loop
  f-g-loop =
    begin
      ap (f ∘ g) loop
    ≡⟨ ap-∘ g f loop ⟩
      ap f (merid true ∙ merid false ⁻¹)
    ≡⟨ ap-∙ f (merid true) (merid false ⁻¹) ⟩
      loop ∙ ap f (merid false ⁻¹)
    ≡⟨ ap (_∙_ loop) (ap-⁻¹ f (merid false)) ⟩
      loop ∙ refl base
    ≡⟨ p∙refl≡p loop ⟩
      loop
    ∎

  f-g-tr-loop : refl base ≡ refl base [ (λ s → (f ∘ g) s ≡ s) ↓ loop ]
  f-g-tr-loop =
    begin
      transport (λ s → (f ∘ g) s ≡ s) loop (refl base)
    ≡⟨ ↓-ap (f ∘ g) id loop (refl base) ⟩
      ap (f ∘ g) loop ⁻¹ ∙ refl base ∙ ap id loop
    ≡⟨ ap (λ p → ap (f ∘ g) loop ⁻¹ ∙ refl base ∙ p) (ap-id loop) ⟩
      ap (f ∘ g) loop ⁻¹ ∙ refl base ∙ loop
    ≡⟨ ∙-assoc (ap (f ∘ g) loop ⁻¹) (refl base) loop ⟩
      ap (f ∘ g) loop ⁻¹ ∙ (refl base ∙ loop)
    ≡⟨ ap (λ p → ap (f ∘ g) loop ⁻¹ ∙ p) (refl∙p≡p loop) ⟩
      ap (f ∘ g) loop ⁻¹ ∙ loop
    ≡⟨ ap (λ p → p ⁻¹ ∙ loop) f-g-loop ⟩
      loop ⁻¹ ∙ loop
   ≡⟨ p⁻¹∙p≡refl loop ⟩
      refl base
    ∎

  f-g : f ∘ g ~ id
  f-g = ind-S¹ (λ s → f (g s) ≡ s) (refl (f (g base))) f-g-tr-loop

∑bool≃S¹ : ∑ bool ≃ S¹
∑bool≃S¹ = let open ∑bool≃S¹ in
  f , record { g = g
             ; f-g = f-g
             ; g-f = g-f
             }

∑bool≡S¹ : ∑ bool ≡ S¹
∑bool≡S¹ with ua
... | _ , eq = is-equiv.g eq ∑bool≃S¹

S¹≡∑bool : S¹ ≡ ∑ bool
S¹≡∑bool = ∑bool≡S¹ ⁻¹
