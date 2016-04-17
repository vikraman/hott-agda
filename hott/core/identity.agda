{-# OPTIONS --without-K --rewriting #-}

module hott.core.identity where

infix 4 _≡_

data _≡_ {ℓ} {A : Set ℓ} : A → A → Set ℓ where
  refl : (a : A) → a ≡ a

{-# BUILTIN REWRITE _≡_ #-}

module _ {a} {A : Set a} {x : A} where

  infixl 90 _⁻¹

  _⁻¹ : {y : A} → x ≡ y → y ≡ x
  refl _ ⁻¹ = refl x

module _ {a b} {A : Set a} {B : Set b} {x : A} where

  ap : {y : A} → (f : A → B) → x ≡ y → f x ≡ f y
  ap f (refl _) = refl (f x)

  syntax ap f p = f |> p

module _ {a p} {A : Set a} (P : A → Set p) {x : A} where

  transport : {y : A} → x ≡ y → P x → P y
  transport (refl _) p = p

  PathOver : {y : A} → x ≡ y → P x → P y → Set p
  PathOver p u v = transport p u ≡ v

  syntax PathOver P p u v = u ≡ v [ P ↓ p ]

module _ {a p} {A : Set a} {P : A → Set p} {x : A} where

  _* : {y : A} → x ≡ y → P x → P y
  _* = transport P

module _ {a b} {A : Set a} {B : A → Set b} {x : A} where

  apd : {y : A} → (f : (x : A) → B x)
      → (p : x ≡ y) → f x ≡ f y [ B ↓ p ]
  apd f (refl _) = refl (f x)

module _ {a} {A : Set a} {x : A} where

  infixl 70 _∙_

  _∙_ : {y z : A} → x ≡ y → y ≡ z → x ≡ z
  (refl _) ∙ (refl _) = refl x

module _ {a} {A : Set a} where

  infix 1 begin_
  infixr 2 _≡⟨_⟩_
  infix 3 _∎

  begin_ : {x y : A} → x ≡ y → x ≡ y
  begin p = p

  _∎ : (x : A) → x ≡ x
  x ∎ = refl x

  _≡⟨_⟩_ : {y z : A} (x : A) → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ p ⟩ q = p ∙ q
