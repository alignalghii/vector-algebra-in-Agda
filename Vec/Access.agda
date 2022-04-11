module Vec.Access where

open import Vec.Base using (Vec; []; _∷_)
open import Nat.Base using (ℕ)
open import Fin.Base using (Fin; fZero; fSucc)


_[_] : ∀ {A : Set} {n : ℕ} → Vec A n → Fin n → A
(a ∷ as) [ fZero   ] = a
(_ ∷ as) [ fSucc i ] = as [ i ]
