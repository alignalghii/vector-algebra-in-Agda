module Rational.Base where

open import Rational.Unsigned using (ℚ₀₊; frac; _≡ₓ_)
open import Nat.Base using (ℕ; O)
open import Logic.Bool using (𝟚)  -- sign for transitioning from ℚ₀₊ to ℚ
open import Logic.Eq using (_≢_)


record ℚ : Set where
    constructor
        _,_
    field
        sign          : 𝟚
        absoluteValue : ℚ₀₊

open ℚ


-- Equivalence among (signed) rationals:

infix 4 _≡∷_
data _≡∷_ : ℚ → ℚ → Set where
   eq-by-sign-zero     : ∀ (sgn : 𝟚) (n₁ n₂ : ℕ) (cnstrnt₁ : n₁ ≢ O) (cnstrnt₂ : n₂ ≢ O) → (sgn , frac O n₁ cnstrnt₁) ≡∷ (sgn , frac O n₂ cnstrnt₂)
   eq-by-abs-crossmult : ∀ (sgn : 𝟚) (abs₁ abs₂ : ℚ₀₊) → abs₁ ≡ₓ abs₂                    → (sgn , abs₁              ) ≡∷ (sgn , abs₂              )
