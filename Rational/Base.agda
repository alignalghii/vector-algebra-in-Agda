module Rational.Base where

open import Logic.Bool using (𝟚)  -- Use later to introduce sign when transitioning from ℚ₀₊ to ℚ
open import Nat.Base using (ℕ; O)
open import Logic.Eq using (_≢_)


data ℚ₀₊ : Set where
    frac₀₊ : ∀ (m n : ℕ) → n ≢ O → ℚ₀₊
