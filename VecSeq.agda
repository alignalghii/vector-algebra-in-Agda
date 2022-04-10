module VecSeq where

open import Vec
open import Nat
open import Fin
open import NatNotation
open import FinNotation
open import Eq


seq : ∀ (n : ℕ) → Vec (Fin n) n
seq O = []
seq (S n) = fzero ∷ vMap fsucc (seq n)

seq-sample₁ : seq #4 ≡ #0₄ ∷ #1₄ ∷ #2₄ ∷ #3₄ ∷ []
seq-sample₁ = refl
