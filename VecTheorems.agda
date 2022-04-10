module VecTheorems where

open import Vec using (Vec; []; _∷_)
open import VecAccess using (at)
open import Fin using (Fin; fzero; fsucc)

open import NatNotation using (#0; #1; #2)
open import FinNotation using (#0₃; #1₃; #2₃)
open import Eq using (_≡_; refl)


at-example₁ : at (#2 ∷ #1 ∷ #0 ∷ []) #0₃ ≡ #2
at-example₁ = refl

at-example₂ : at (#2 ∷ #1 ∷ #0 ∷ []) #1₃ ≡ #1
at-example₂ = refl

at-example₃ : at (#2 ∷ #1 ∷ #0 ∷ []) #2₃ ≡ #0
at-example₃ = refl
