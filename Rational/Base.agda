module Rational.Base where

open import Rational.Unsigned using (ℚ₀₊; frac; _≡ₓ_; |½|; |⅓|; |²/₆|; |⁰/₂|; |⁰/₃|)
open import Nat.Base using (ℕ; O)
open import Logic.Bool using (𝟚) renaming (true to plus; false to minus)  -- sign for transitioning from ℚ₀₊ to ℚ
open import Logic.Eq using (refl; _≢_)
open import Logic.Absurd using (¬_)


record ℚ : Set where
    constructor
        _,_
    field
        sign          : 𝟚
        absoluteValue : ℚ₀₊

open ℚ


-- Equivalence among (signed) rationals:

infix 4 _≡∷_ _≢∷_
data _≡∷_ : ℚ → ℚ → Set where
   eq-by-sign-zero     : ∀ (sgn : 𝟚) (n₁ n₂ : ℕ) (cnstrnt₁ : n₁ ≢ O) (cnstrnt₂ : n₂ ≢ O) → (sgn , frac O n₁ cnstrnt₁) ≡∷ (sgn , frac O n₂ cnstrnt₂)
   eq-by-abs-crossmult : ∀ (sgn : 𝟚) (abs₁ abs₂ : ℚ₀₊) → abs₁ ≡ₓ abs₂                    → (sgn , abs₁              ) ≡∷ (sgn , abs₂              )

_≢∷_ : ℚ → ℚ → Set
q₁ ≢∷ q₂ = ¬(q₁ ≡∷ q₂)

-- Examples:

+½ -½ +⅓ -⅓ +²/₆ -²/₆ +⁰/₂ -⁰/₂ +⁰/₃ -⁰/₃ : ℚ
+½   = (plus  , |½|  )
-½   = (minus , |½|  )
+⅓   = (plus  , |⅓|  )
-⅓   = (minus , |⅓|  )
+²/₆ = (plus  , |²/₆|)
-²/₆ = (minus , |²/₆|)
+⁰/₂ = (plus  , |⁰/₂|)
-⁰/₂ = (minus , |⁰/₂|)
+⁰/₃ = (plus  , |⁰/₃|)
-⁰/₃ = (minus , |⁰/₃|)

+½≡+½ : +½ ≡∷ +½
+½≡+½ = eq-by-abs-crossmult plus |½| |½| refl

+⅓≡+²/₆ : +⅓ ≡∷ +²/₆
+⅓≡+²/₆ = eq-by-abs-crossmult plus |⅓| |²/₆| refl

+½≢-½ : +½ ≢∷ -½
+½≢-½ ()
