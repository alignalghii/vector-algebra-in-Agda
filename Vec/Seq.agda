module Vec.Seq where

open import Vec.Base
open import Nat.Base
open import Fin.Base
open import Nat.Notation
open import Fin.Notation
open import Eq


seq : ∀ (n : ℕ) → Vec (Fin n) n
seq O = []
seq (S n) = fZero ∷ vMap fSucc (seq n)

seq-sample₁ : seq #4 ≡ #0₄ ∷ #1₄ ∷ #2₄ ∷ #3₄ ∷ []
seq-sample₁ = refl
