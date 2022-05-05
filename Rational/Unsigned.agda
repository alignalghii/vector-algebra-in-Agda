module Rational.Unsigned where

open import Nat.Base using (ℕ; O; _⋅_)
open import Logic.Eq using (_≡_; _≢_)


-- Division-by-zero constraint on denominator:

data ℚ₀₊ : Set where
    frac : ∀ (m n : ℕ) → n ≢ O → ℚ₀₊

-- Equivalence of fractions is the cross-multiplication equivalence of proportions:

infix 4 _≡ₓ_
_≡ₓ_ : ℚ₀₊ → ℚ₀₊ → Set
frac m₁ n₁ _ ≡ₓ frac m₂ n₂ _ = m₁ ⋅ n₂ ≡ m₂ ⋅ n₁
