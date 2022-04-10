module VecAccess where

open import Vec using (Vec; []; _∷_)
open import Nat using (ℕ)
open import Fin using (Fin; fzero; fsucc)


_[_] : ∀ {A : Set} {n : ℕ} → Vec A n → Fin n → A
(a ∷ as) [ fzero   ] = a
(_ ∷ as) [ fsucc i ] = as [ i ]
