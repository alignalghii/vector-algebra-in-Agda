module Vec.Matrix.TranspositionAlternative where

open import Vec.Matrix.Base using (Matrix)
open import Vec.Matrix.Transposition using (transpose)
open import Vec.Matrix.RowsAndColumns using (_[*,_])
open import Vec.Base using (vMap)
open import Vec.Seq using (seq)
open import Nat.Base using (ℕ)
open import Fin.Base using (Fin)
open import Eq using (_≡_)


transpose' : ∀ {A : Set} {m n : ℕ} → Matrix A m n → Matrix A n m
transpose' {n = n} mat = vMap (mat [*,_]) (seq n)

postulate transposition-has-alternative-definitions : ∀ {A : Set} {m n : ℕ} (mat : Matrix A m n) → transpose mat ≡ transpose' mat
