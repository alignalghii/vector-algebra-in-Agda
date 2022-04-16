module Fin.Base where

open import Nat.Base using (ℕ; O; S)


data Fin : ℕ → Set where
    fZero : ∀ {n : ℕ} → Fin (S n)
    fSucc : ∀ {n : ℕ} → Fin n → Fin (S n)

fLast : ∀ {n : ℕ} → Fin (S n)
fLast {O}   = fZero
fLast {S _} = fSucc fLast
