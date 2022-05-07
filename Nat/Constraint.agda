module Nat.Constraint where

open import Nat.Base using (ℕ; O; S)
open import Logic.Eq using (_≢_)


≢0 : ∀ {n : ℕ} → S n ≢ O
≢0 ()
