module Vec.Theorems where

open import Vec.Base using (Vec; []; _∷_)
open import Vec.Access using (_[_])
open import Fin.Base using (Fin; fZero; fSucc)

open import Nat.Notation using (#0; #1; #2)
open import Fin.Notation using (#0₃; #1₃; #2₃)
open import Logic.Eq using (_≡_; refl)


*[*]-example₁ : (#2 ∷ #1 ∷ #0 ∷ []) [ #0₃ ] ≡ #2
*[*]-example₁ = refl

*[*]-example₂ : (#2 ∷ #1 ∷ #0 ∷ []) [ #1₃ ] ≡ #1
*[*]-example₂ = refl

*[*]-example₃ : (#2 ∷ #1 ∷ #0 ∷ []) [ #2₃ ] ≡ #0
*[*]-example₃ = refl

head-example₁ : (#2 ∷ #1 ∷ #0 ∷ []) [ #2₃ ] ≡ #0
head-example₁ = refl

vLast-example₁ : (#2 ∷ #1 ∷ #0 ∷ []) [ #2₃ ] ≡ #0
vLast-example₁ = refl
