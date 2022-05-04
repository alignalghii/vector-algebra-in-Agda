module Vec.Access where

open import Vec.Base using (Vec; []; _∷_)
open import Nat.Base using (ℕ; S)
open import Fin.Base using (Fin; fZero; fSucc; fLast)
open import Logic.Eq using (_≡_; refl; ≡-congruence₂)
open import Logic.Combinators using (_∘_)


-- Note that the following does not work: `_[_] : ∀ {A : Set} {n : ℕ} → Vec A (S n) → Fin (S n) → A`
-- at leat for the constructor patterns below.
-- Agda seems to be sensible for such unnecesiary restriction for the possibly universially quantified absurd cases:
--- they are and must be left valid.
-- Probably `Fin O` automatically handles the absurd case:

_[_] : ∀ {A : Set} {n : ℕ} → Vec A n → Fin n → A
(a ∷ as) [ fZero   ] = a
(_ ∷ as) [ fSucc i ] = as [ i ]

-- Also this vector-extensionality function demostrates
-- that it is important to be able to make statements for universally quantified absurd cases:

vExtensionality : ∀ {A : Set} {n : ℕ} (as₁ as₂ : Vec A n) → (∀ (i : Fin n) → as₁ [ i ] ≡ as₂ [ i ]) → as₁ ≡ as₂
vExtensionality         []         []         _     = refl
vExtensionality {A} {n} (a₁ ∷ as₁) (a₂ ∷ as₂) extEq = ≡-congruence₂ {A} {Vec A n} _∷_ (extEq fZero) (vExtensionality as₁ as₂ (extEq ∘ fSucc))

head vLast : ∀ {A : Set} {n : ℕ} → Vec A (S n) → A
head = _[ fZero ]
vLast = _[ fLast ]

-- Obsolete theorems, but only if head is not defined directly:
-- If head is defined directly, head-is-first must be given a `_ ∷ _` pattern explicitely

-- head-is-first : ∀ {A : Set} {n : ℕ} (as : Vec A (S n)) → head as ≡ as [ fZero ]
-- head-is-first _ = refl

-- vLast-is-last : ∀ {A : Set} {n : ℕ} (as : Vec A (S n)) → vLast as ≡ as [ fLast ]
-- vLast-is-last _ = refl

tail : ∀ {A : Set} {n : ℕ} → Vec A (S n) → Vec A n
tail (_ ∷ as) = as

-- TODO: had is defined by sequencing, tail is defined by pattern matching
-- There are two definition alternatives both for head and for tail
-- Prove the equivalence of these alternatives!
-- See also Vec/Matrix/ShipwreckedTheorems
