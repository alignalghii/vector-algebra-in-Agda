module VecMatrix where

open import Vec using (Vec; []; _∷_; vMap; vZipWith; vReplicate)
open import VecAccess using (_[_])
open import Nat using (ℕ; O; S)
open import NatNotation using (#0; #1; #2; #3)
open import Fin using (Fin; fzero)
open import FinNotation using (#1₂; #2₄)
open import VecSeq using (seq)
open import Eq using (_≡_; refl; ≡-congruence)


Matrix : Set → ℕ → ℕ → Set
Matrix = λ A m n → Vec (Vec A n) m

column : ∀ {A : Set} {m n : ℕ} → Matrix A m n → Fin n → Vec A m
column rows j = vMap _[ j ] rows

preponeColumn : ∀ {A : Set} {m n : ℕ} → Vec A m → Matrix A m n → Matrix A m (S n)
preponeColumn column rows = vZipWith (_∷_) column rows

_[_,_] : ∀ {A : Set} {m n : ℕ} → Matrix A m n → Fin m → Fin n → A
rows [ i , j ] = rows [ i ] [ j ]

*[*,*]-sample₁ : (   (#0 ∷ #1 ∷ #2 ∷ #3 ∷ []) ∷
                     (#3 ∷ #2 ∷ #1 ∷ #0 ∷ []) ∷ []
                 )
                 [ #1₂ , #2₄ ]
                 ≡
                 #1
*[*,*]-sample₁ = refl

transpose : ∀ {A : Set} {m n : ℕ} → Matrix A m n → Matrix A n m
transpose {n = n} rows = vMap (column rows) (seq n)

transpose-sample₁ : transpose (   (#0 ∷ #1 ∷ #2 ∷ #3 ∷ []) ∷
                                  (#3 ∷ #2 ∷ #1 ∷ #0 ∷ []) ∷ []
                              )
                              ≡
                                  (#0 ∷ #3 ∷ []) ∷
                                  (#1 ∷ #2 ∷ []) ∷
                                  (#2 ∷ #1 ∷ []) ∷
                                  (#3 ∷ #0 ∷ []) ∷ []
transpose-sample₁ = refl

transpose-empty-lemma : ∀ {A : Set} {n : ℕ} (degeneratedHorizontalMatrix : Matrix A O n) → transpose degeneratedHorizontalMatrix ≡ vReplicate n []
transpose-empty-lemma {n = O   } [] = refl
transpose-empty-lemma {n = S n'} [] = ≡-congruence ([] ∷_) transpose-empty-lemma {n = n'} []

transpose-prepone-lemma : ∀ {A : Set} {m n : ℕ} (row : Vec A n) (rows : Matrix A m n) → transpose (row ∷ rows) ≡ preponeColumn row (transpose rows)
transpose-prepone-lemma [] [] = refl

row-to-column : ∀ {A : Set} {m n : ℕ} (rows : Matrix A m n) (i : Fin m) → rows [ i ] ≡ column (transpose rows) i
row-to-column ([]       ∷ rows) fzero = refl
row-to-column ((a ∷ []) ∷ rows) fzero = refl
-- row-to-column ((a ∷ as) ∷ []  ) fzero = row-to-column (as ∷ []) fzero

postulate transpose-is-involution : ∀ {A : Set} {m n : ℕ} (rows : Matrix A m n) → transpose (transpose rows) ≡ rows
-- TODO
