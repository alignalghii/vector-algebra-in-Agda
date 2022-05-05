module Rational.Base where

open import Rational.AbsoluteValue using (ℚ₀₊)
open import Logic.Bool using (𝟚)


record ℚ : Set where
    field
        sign          : 𝟚
        absoluteValue : ℚ₀₊
