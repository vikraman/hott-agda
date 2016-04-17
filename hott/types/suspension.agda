{-# OPTIONS --rewriting #-}

module hott.types.suspension where

open import hott.core

module _ {a} where
  postulate
    ∑_ : (A : Set a) → Set a

  module _ {A : Set a} where
    postulate
      𝑁 : ∑ A
      𝑆 : ∑ A
      merid : (a : A) → 𝑁 ≡ 𝑆

module _ {a p} {A : Set a}
         (P : Set p) (𝑛 𝑠 : P)
         (𝑚 : A → 𝑛 ≡ 𝑠) where
  postulate
    rec-∑ : ∑ A → P
    βrec-∑-𝑁 : rec-∑ 𝑁 ≡ 𝑛
    βrec-∑-𝑆 : rec-∑ 𝑆 ≡ 𝑠
    {-# REWRITE βrec-∑-𝑁 #-}
    {-# REWRITE βrec-∑-𝑆 #-}
    βrec-∑-merid : (a : A) → ap rec-∑ (merid a) ≡ 𝑚 a

module _ {a p} {A : Set a}
         (P : ∑ A → Set p) (𝑛 : P 𝑁) (𝑠 : P 𝑆)
         (𝑚 : (a : A) → 𝑛 ≡ 𝑠 [ P ↓ merid a ]) where
  postulate
    ind-∑ : (x : ∑ A) → P x
    βind-∑-𝑁 : ind-∑ 𝑁 ≡ 𝑛
    βind-∑-𝑆 : ind-∑ 𝑆 ≡ 𝑠
    {-# REWRITE βind-∑-𝑁 #-}
    {-# REWRITE βind-∑-𝑆 #-}
    βind-∑-merid : (a : A) → apd ind-∑ (merid a) ≡ 𝑚 a
