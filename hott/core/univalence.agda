{-# OPTIONS --without-K #-}

module hott.core.univalence where

open import hott.core.equivalence
open import hott.core.identity

module _ {ℓ} {A B : Set ℓ} where
  postulate
    ua : (A ≡ B) ≃ (A ≃ B)

module _ {a b} {A : Set a} {B : Set b} where

  happly : {f g : A → B} → f ≡ g → (x : A) → f x ≡ g x
  happly (refl h) x = refl (h x)

  postulate
    funext : {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g
    happly-funext : {f g : A → B}
                  → (h : (x : A) → f x ≡ g x) (x : A)
                  → happly (funext h) x ≡ h x
