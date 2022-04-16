module Vec.Access where

open import Vec.Base using (Vec; []; _∷_)
open import Nat.Base using (ℕ; S)
open import Fin.Base using (Fin; fZero; fSucc; fLast)
open import Eq using (_≡_; refl)


-- Note that the following does not work: `_[_] : ∀ {A : Set} {n : ℕ} → Vec A (S n) → Fin (S n) → A`
-- Probably `Fin O` automatically handles the empty function case:

_[_] : ∀ {A : Set} {n : ℕ} → Vec A n → Fin n → A
(a ∷ as) [ fZero   ] = a
(_ ∷ as) [ fSucc i ] = as [ i ]

head tail : ∀ {A : Set} {n : ℕ} → Vec A (S n) → A
head = _[ fZero ]
tail = _[ fLast ]

-- Obsolete theorems, but only if head is not defined directly:
-- If head is defined directly, head-is-first must be given a `_ ∷ _` pattern explicitely

-- head-is-first : ∀ {A : Set} {n : ℕ} (as : Vec A (S n)) → head as ≡ as [ fZero ]
-- head-is-first _ = refl

-- tail-is-last : ∀ {A : Set} {n : ℕ} (as : Vec A (S n)) → tail as ≡ as [ fLast ]
-- tail-is-last _ = refl
