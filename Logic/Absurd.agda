module Logic.Absurd where


data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥
