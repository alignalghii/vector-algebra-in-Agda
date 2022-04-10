module VecTheorems where

open import Vec using (Vec; []; _∷_)
open import VecAccess using (_[_])
open import Fin using (Fin; fZero; fSucc)

open import NatNotation using (#0; #1; #2)
open import FinNotation using (#0₃; #1₃; #2₃)
open import Eq using (_≡_; refl)


*[*]-example₁ : (#2 ∷ #1 ∷ #0 ∷ []) [ #0₃ ] ≡ #2
*[*]-example₁ = refl

*[*]-example₂ : (#2 ∷ #1 ∷ #0 ∷ []) [ #1₃ ] ≡ #1
*[*]-example₂ = refl

*[*]-example₃ : (#2 ∷ #1 ∷ #0 ∷ []) [ #2₃ ] ≡ #0
*[*]-example₃ = refl
