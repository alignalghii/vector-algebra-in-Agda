module Logic.Absurd where


data ⊥ : Set where
    -- it has no constructors

¬_ : Set → Set
¬ A = A → ⊥
