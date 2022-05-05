module Rational.AbsoluteValue where

open import Nat.Base using (ℕ; O; _⋅_)
open import Logic.Eq using (_≡_; _≢_)


data ℚ₀₊ : Set where
    frac : ∀ (m n : ℕ) → n ≢ O → ℚ₀₊

infix 4 _≡∷₀₊_
_≡∷₀₊_ : ℚ₀₊ → ℚ₀₊ → Set
frac m₁ n₁ _ ≡∷₀₊ frac m₂ n₂ _ = m₁ ⋅ n₂ ≡ m₂ ⋅ n₁
