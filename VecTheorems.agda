module VecTheorems where

open import Vec using (Vec; []; _∷_)
open import VecAccess using (_[_])
open import Fin using (Fin; fzero; fsucc)

open import NatNotation using (#0; #1; #2)
open import FinNotation using (#0₃; #1₃; #2₃)
open import Eq using (_≡_; refl)


_[_]-example₁ : (#2 ∷ #1 ∷ #0 ∷ []) [ #0₃ ] ≡ #2
_[_]-example₁ = refl

_[_]-example₂ : (#2 ∷ #1 ∷ #0 ∷ []) [ #1₃ ] ≡ #1
_[_]-example₂ = refl

_[_]-example₃ : (#2 ∷ #1 ∷ #0 ∷ []) [ #2₃ ] ≡ #0
_[_]-example₃ = refl
