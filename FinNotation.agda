module FinNotation where

open import Fin using (Fin; fzero; fsucc)
open import Nat using (ℕ)
open import NatNotation


#0₁ : Fin #1
#0₁ = fzero

#0₂ #1₂ : Fin #2
#0₂ = fzero
#1₂ = fsucc #0₁

#0₃ #1₃ #2₃ : Fin #3
#0₃ = fzero
#1₃ = fsucc #0₂
#2₃ = fsucc #1₂

#0₄ #1₄ #2₄ #3₄ : Fin #4
#0₄ = fzero
#1₄ = fsucc #0₃
#2₄ = fsucc #1₃
#3₄ = fsucc #2₃
