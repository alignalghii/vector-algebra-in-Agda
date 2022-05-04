module Rational.Base where

open import Logic.Bool using (𝟚)  -- Use later to introduce sign when transitioning from ℚ₀₊ to ℚ
open import Nat.Base using (ℕ; O; _⋅_)
open import Logic.Eq using (_≡_; _≢_)


data ℚ₀₊ : Set where
    frac : ∀ (m n : ℕ) → n ≢ O → ℚ₀₊

infix 4 _≡∷_
_≡∷_ : ℚ₀₊ → ℚ₀₊ → Set
frac m₁ n₁ _ ≡∷ frac m₂ n₂ _ = m₁ ⋅ n₂ ≡ m₂ ⋅ n₁
