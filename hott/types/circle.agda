{-# OPTIONS --rewriting #-}

module hott.types.circle where

open import hott.core

postulate
  S¹ : Set
  base : S¹
  loop : base ≡ base

module _ {p} (P : Set p) (pbase : P) (ploop : pbase ≡ pbase) where
  postulate
    rec-S¹ : S¹ → P
    βrec-S¹-base : rec-S¹ base ≡ pbase
    {-# REWRITE βrec-S¹-base #-}
    βrec-S¹-loop : ap rec-S¹ loop ≡ ploop

module _ {p} (P : S¹ → Set p) (pbase : P base)
         (ploop : pbase ≡ pbase [ P ↓ loop ]) where
  postulate
    ind-S¹ : (s : S¹) → P s
    βind-S¹-base : ind-S¹ base ≡ pbase
    {-# REWRITE βind-S¹-base #-}
    βind-S¹-loop : apd ind-S¹ loop ≡ ploop
