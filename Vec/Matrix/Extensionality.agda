module Vec.Matrix.Extensionality where

open import Vec.Matrix.Base using (Matrix; _[_,_])
open import Vec.Access using (vExtensionality; _[_])
open import Nat.Base using (ℕ)
open import Fin.Base using (Fin)
open import Logic.Eq using (_≡_)


matrix-extensionality : ∀ {A : Set} {m n : ℕ} (mat₁ mat₂ : Matrix A m n) → (∀ (i : Fin m) (j : Fin n) → mat₁ [ i , j ] ≡ mat₂ [ i , j ]) → mat₁ ≡ mat₂
matrix-extensionality mat₁ mat₂ extEq = vExtensionality mat₁ mat₂ (λ i → vExtensionality (mat₁ [ i ]) (mat₂ [ i ]) (extEq i))

Index-keeping : ∀ {A : Set} {m n : ℕ} → (Matrix A m n → Matrix A m n) → Set
Index-keeping {A} {m} {n} op = ∀ (mat : Matrix A m n) (i : Fin m) (j : Fin n) → mat [ i , j ] ≡ (op mat) [ i , j ]

index-keeping-implies-extensional-identity : ∀ {A : Set} {m n : ℕ} → (op : Matrix A m n → Matrix A m n) (mat : Matrix A m n) → (∀ (i : Fin m) (j : Fin n) → mat [ i , j ] ≡ (op mat) [ i , j ]) → mat ≡ op mat
index-keeping-implies-extensional-identity op mat op-is-keeping-on-mat = matrix-extensionality mat (op mat) op-is-keeping-on-mat
