module Rational.Base where

open import Logic.Bool using (𝟚)
open import Nat.Base using (ℕ)


data ℚ : Set where
    zero-ℚ : ℚ
    frac-ℚ : 𝟚 → ℕ → ℕ → ℚ
