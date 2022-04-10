module VecAccess where

open import Vec using (Vec; []; _∷_)
open import Nat using (ℕ)
open import Fin using (Fin; fZero; fSucc)


_[_] : ∀ {A : Set} {n : ℕ} → Vec A n → Fin n → A
(a ∷ as) [ fZero   ] = a
(_ ∷ as) [ fSucc i ] = as [ i ]
