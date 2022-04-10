module VecAccess where

open import Vec using (Vec; []; _∷_)
open import Nat using (ℕ)
open import Fin using (Fin; fzero; fsucc)


-- _[_] : ∀ {A : Set} {n : ℕ} → Vec A n → Fin n → A
-- (a ∷ as)[fzero  ] = a
-- (a ∷ as)[fsucc i] = as[i]

at : ∀ {A : Set} {n : ℕ} → Vec A n → Fin n → A
at (a ∷ as) fzero    = a
at (a ∷ as)(fsucc i) = at  as i
