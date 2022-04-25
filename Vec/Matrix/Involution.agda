module Vec.Matrix.Involution where

open import Vec.Matrix.Extensionality using (matrix-extensionality; Index-keeping)
open import Vec.Matrix.Base using (Matrix; _[_,_])
open import Nat.Base using (ℕ)
open import Fin.Base using (Fin)
open import Eq using (_≡_; ≡-transitivity)
open import Combinators using (_∘_)


Index-swapping : ∀ {A : Set} {m n : ℕ} → (Matrix A m n → Matrix A n m) → Set
Index-swapping {A} {m} {n} op = ∀ (mat : Matrix A m n) (i : Fin m) (j : Fin n) → mat [ i , j ] ≡ (op mat) [ j , i ]

index-double-swapping-is-keeping : ∀ {A : Set} {m n : ℕ} (op : ∀ {m' n' : ℕ} → Matrix A m' n' → Matrix A n' m') → (∀ {m, n, : ℕ} → Index-swapping (op {m,} {n,})) → Index-keeping {A} {m} {n} (op ∘ op)
index-double-swapping-is-keeping op op-is-swapping mat i j = ≡-transitivity (op-is-swapping mat i j) (op-is-swapping (op mat) j i)

index-swapping-implies-involution : ∀ {A : Set} {m n : ℕ} (op : ∀ {m' n' : ℕ} → Matrix A m' n' → Matrix A n' m') → (∀ {m, n, : ℕ} → Index-swapping (op {m,} {n,})) → ∀ (mat : Matrix A m n) → mat ≡ op (op mat)
index-swapping-implies-involution op op-is-swapping mat = matrix-extensionality mat (op (op mat)) (index-double-swapping-is-keeping op op-is-swapping mat)
