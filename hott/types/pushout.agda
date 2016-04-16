{-# OPTIONS --rewriting #-}

module hott.types.pushout where

open import hott.core
open import hott.types.span

module _ {a b c} where
  postulate
    pushout : span {a} {b} {c} → Set (suc (a ⊔ b ⊔ c))

  module _ {s : span {a} {b} {c}} where
    open span s
    postulate
      inl : A → pushout s
      inr : B → pushout s
      glue : (c : C) → inl (f c) ≡ inr (g c)

module _ {a b c p} {s : span {a} {b} {c}} (P : Set p) where
  open span s
  module _ (𝑙 : A → P) (𝑟 : B → P) (𝑔 : (c : C) → 𝑙 (f c) ≡ 𝑟 (g c)) where
    postulate
      rec-pushout : pushout s → P
      β-rec-pushout-𝑙 : (a : A) → rec-pushout (inl a) ≡ 𝑙 a
      β-rec-pushout-𝑟 : (b : B) → rec-pushout (inr b) ≡ 𝑟 b
      {-# REWRITE β-rec-pushout-𝑙 #-}
      {-# REWRITE β-rec-pushout-𝑟 #-}
      β-rec-pushout-glue : (c : C) → ap rec-pushout (glue c) ≡ 𝑔 c

module _ {a b c p} {s : span {a} {b} {c}} (P : pushout s → Set p) where
  open span s
  module _ (𝑙 : (a : A) → P (inl a)) (𝑟 : (b : B) → P (inr b))
           (𝑔 : (c : C) → 𝑙 (f c) ≡ 𝑟 (g c) [ P ↓ glue c ]) where
    postulate
      ind-pushout : (p : pushout s) → P p
      β-ind-pushout-𝑙 : (a : A) → ind-pushout (inl a) ≡ 𝑙 a
      β-ind-pushout-𝑟 : (b : B) → ind-pushout (inr b) ≡ 𝑟 b
      {-# REWRITE β-ind-pushout-𝑙 #-}
      {-# REWRITE β-ind-pushout-𝑟 #-}
      β-ind-pushout-glue : (c : C) → apd ind-pushout (glue c) ≡ 𝑔 c
