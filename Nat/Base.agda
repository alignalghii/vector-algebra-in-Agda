module Nat.Base where

open import Logic.Eq


data ℕ : Set where
    O : ℕ
    S : ℕ → ℕ

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
m + O     = m          -- + has right-neutral
m + (S n) = S (m + n)  -- + is  right-recurrible

+-has-left-neutral : ∀ (n : ℕ) → O + n ≡ n
+-has-left-neutral O      = refl
+-has-left-neutral (S n') = ≡-congruence S (+-has-left-neutral n')

+-is-left-recurrible : ∀ (m n : ℕ) → S m + n ≡ S (m + n)
+-is-left-recurrible m O      = refl
+-is-left-recurrible m (S n') = ≡-congruence S (+-is-left-recurrible m n')

+-commutativity : ∀ (m n : ℕ) → m + n ≡ n + m
+-commutativity m O      = ≡-symmetry (+-has-left-neutral m)
+-commutativity m (S n') = ≡-transitivity (≡-congruence S (+-commutativity m n')) (≡-symmetry (+-is-left-recurrible n' m))


infixl 7 _⋅_
_⋅_ : ℕ → ℕ → ℕ
m ⋅ O     = O          -- ⋅ has right-neutral
m ⋅ (S n) = m ⋅ n + m  -- ⋅ is  right-recurrible
