module Vec.Base where

open import Nat.Base using (ℕ; O; S; _+_; +-commutativity)
open import Eq


data Vec (A : Set) : ℕ → Set where
    [] : Vec A O
    _∷_ : ∀ {n : ℕ} → A → Vec A n → Vec A (S n)

infixr 5 _∷_

infixr 5 _++'_ _++_
_++'_ : ∀ {A : Set} {m n : ℕ} → Vec A m → Vec A n → Vec A (n + m)
[]         ++' as₂ = as₂
(a₁ ∷ as₁) ++' as₂ = a₁ ∷ (as₁ ++' as₂)

_++_ : ∀ {A : Set} {m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
_++_ {A} {m} {n} u v = subst (Vec A) (+-commutativity n m) (u ++' v)


last  : ∀ {A : Set} {n : ℕ} → Vec A (S n) → A
last (a₁ ∷ []     ) = a₁
last (_  ∷ a₂ ∷ as) = last (a₂ ∷ as)

vMap : ∀ {A B : Set} {n : ℕ} → (A → B) → Vec A n → Vec B n
vMap _ []       = []
vMap f (a ∷ as) = f a ∷ vMap f as

vZipWith : ∀ {A B C : Set} {n : ℕ} → (A → B → C) → Vec A n → Vec B n → Vec C n
vZipWith _ []       []       = []
vZipWith f (a ∷ as) (b ∷ bs) = f a b ∷ vZipWith f as bs

vReplicate : ∀ {A : Set} (n : ℕ) (a : A) → Vec A n
vReplicate O      _ = []
vReplicate (S n') a = a ∷ vReplicate n' a
