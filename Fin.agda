module Fin where

open import Nat using (ℕ; S)


data Fin : ℕ → Set where
    fzero : ∀ {n : ℕ} → Fin (S n)
    fsucc : ∀ {n : ℕ} → Fin n → Fin (S n)
