{-# OPTIONS --rewriting #-}

module hott.types.interval where

open import hott.core.identity

postulate
  I : Set
  𝟘 : I
  𝟙 : I
  𝑢 : 𝟘 ≡ 𝟙

module _ {p} (P : Set p) (p𝟘 p𝟙 : P) (p𝑢 : p𝟘 ≡ p𝟙) where
  postulate
    rec-I : (i : I) → P
    βrec-I-𝟘 : rec-I 𝟘 ≡ p𝟘
    βrec-I-𝟙 : rec-I 𝟙 ≡ p𝟙
    {-# REWRITE βrec-I-𝟘 #-}
    {-# REWRITE βrec-I-𝟙 #-}
    βrec-I-𝑢 : ap rec-I 𝑢 ≡ p𝑢

module _ {p} (P : I → Set p)
         (p𝟘 : P 𝟘) (p𝟙 : P 𝟙)
         (p𝑢 : p𝟘 ≡ p𝟙 [ P ↓ 𝑢 ]) where
  postulate
    ind-I : (i : I) → P i
    βind-I-𝟘 : ind-I 𝟘 ≡ p𝟘
    βind-I-𝟙 : ind-I 𝟙 ≡ p𝟙
    {-# REWRITE βind-I-𝟘 #-}
    {-# REWRITE βind-I-𝟙 #-}
    βind-I-𝑢 : apd ind-I 𝑢 ≡ p𝑢
