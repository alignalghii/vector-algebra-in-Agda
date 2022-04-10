module Fin where

open import Nat using (ℕ; S)


data Fin : ℕ → Set where
    fZero : ∀ {n : ℕ} → Fin (S n)
    fSucc : ∀ {n : ℕ} → Fin n → Fin (S n)
