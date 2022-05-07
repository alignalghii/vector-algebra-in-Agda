module Rational.Unsigned where

open import Nat.Base using (ℕ; O; _⋅_)
open import Nat.Notation using (#0; #1; #2; #3; #6)
open import Nat.Exclusion using (≢0)
open import Logic.Eq using (_≡_; refl; _≢_)
open import Logic.Absurd using (¬_)


-- Division-by-zero 0-exclusion constraint on denominator:

data ℚ₀₊ : Set where
    frac : ∀ (m n : ℕ) → n ≢ O → ℚ₀₊

-- Equivalence of fractions is the cross-multiplication equivalence of proportions:

infix 4 _≡ₓ_ _≢ₓ_
_≡ₓ_  _≢ₓ_ : ℚ₀₊ → ℚ₀₊ → Set
frac m₁ n₁ _ ≡ₓ frac m₂ n₂ _ = m₁ ⋅ n₂ ≡ m₂ ⋅ n₁
q₁           ≢ₓ q₂           = ¬(q₁ ≡ₓ q₂)

-- Examples:

|½| |⅓| |²/₆| |⁰/₂| |⁰/₃| : ℚ₀₊
|½|   = frac #1 #2 ≢0
|⅓|   = frac #1 #3 ≢0
|²/₆| = frac #2 #6 ≢0
|⁰/₂| = frac #0 #2 ≢0
|⁰/₃| = frac #0 #3 ≢0

|½|≡|½| : |½| ≡ₓ |½|
|½|≡|½| = refl

|⅓|≡|²/₆| : |⅓| ≡ₓ |²/₆|
|⅓|≡|²/₆| = refl

|⁰/₂|≡|⁰/₃| : |⁰/₂| ≡ₓ |⁰/₃|
|⁰/₂|≡|⁰/₃| = refl

|½|≢|⅓| : |½| ≢ₓ |⅓|
|½|≢|⅓| ()
