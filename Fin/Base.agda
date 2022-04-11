module Fin.Base where

open import Nat.Base using (ℕ; S)


data Fin : ℕ → Set where
    fZero : ∀ {n : ℕ} → Fin (S n)
    fSucc : ∀ {n : ℕ} → Fin n → Fin (S n)
