module VecMatrix where

open import Vec using (Vec; []; _∷_; vmap)
open import VecAccess using (_[_])
open import Nat using (ℕ)
open import NatNotation using (#0; #1; #2; #3)
open import Fin using (Fin)
open import FinNotation using (#1₂; #2₄)
open import VecSeq using (seq)
open import Eq using (_≡_; refl)


Matrix : Set → ℕ → ℕ → Set
Matrix = λ A m n → Vec (Vec A n) m

column : ∀ {A : Set} {m n : ℕ} → Matrix A m n → Fin n → Vec A m
column rows j = vmap _[ j ] rows

_[_,_] : ∀ {A : Set} {m n : ℕ} → Matrix A m n → Fin m → Fin n → A
rows [ i , j ] = rows [ i ] [ j ]

_[_,_]-sample₁ : (   (#0 ∷ #1 ∷ #2 ∷ #3 ∷ []) ∷
                     (#3 ∷ #2 ∷ #1 ∷ #0 ∷ []) ∷ []
                 )
                 [ #1₂ , #2₄ ]
                 ≡
                 #1
_[_,_]-sample₁ = refl

transpose : ∀ {A : Set} {m n : ℕ} → Matrix A m n → Matrix A n m
transpose {n = n} rows = vmap (column rows) (seq n)

transpose-sample₁ : transpose (   (#0 ∷ #1 ∷ #2 ∷ #3 ∷ []) ∷
                                  (#3 ∷ #2 ∷ #1 ∷ #0 ∷ []) ∷ []
                              )
                              ≡
                                  (#0 ∷ #3 ∷ []) ∷
                                  (#1 ∷ #2 ∷ []) ∷
                                  (#2 ∷ #1 ∷ []) ∷
                                  (#3 ∷ #0 ∷ []) ∷ []
transpose-sample₁ = refl

postulate row-to-column : ∀ {A : Set} {m n : ℕ} (rows : Matrix A m n) (i : Fin m) → rows [ i ] ≡ column (transpose rows) i

postulate transpose-is-involution : ∀ {A : Set} {m n : ℕ} (rows : Matrix A m n) → transpose (transpose rows) ≡ rows
-- TODO
