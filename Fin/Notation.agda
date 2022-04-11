module Fin.Notation where

open import Fin.Base using (Fin; fZero; fSucc)
open import Nat.Base using (ℕ)
open import Nat.Notation


#0₁ : Fin #1
#0₁ = fZero

#0₂ #1₂ : Fin #2
#0₂ = fZero
#1₂ = fSucc #0₁

#0₃ #1₃ #2₃ : Fin #3
#0₃ = fZero
#1₃ = fSucc #0₂
#2₃ = fSucc #1₂

#0₄ #1₄ #2₄ #3₄ : Fin #4
#0₄ = fZero
#1₄ = fSucc #0₃
#2₄ = fSucc #1₃
#3₄ = fSucc #2₃
