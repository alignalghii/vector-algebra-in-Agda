module Vec.Matrix where

open import Vec.Base using (Vec; []; _∷_; vMap; vZipWith; vReplicate)
open import Vec.Access using (_[_])
open import Nat.Base using (ℕ; O; S)
open import Nat.Notation using (#0; #1; #2; #3)
open import Fin.Base using (Fin; fZero)
open import Fin.Notation using (#1₂; #2₄)
open import Vec.Seq using (seq)
open import Eq using (_≡_; refl; ≡-congruence)
open import CategoricalTheorems using (is-constant)


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

postulate transpose-empty-lemma : ∀ {A : Set} {n : ℕ} (degeneratedHorizontalMatrix : Matrix A O n) → transpose degeneratedHorizontalMatrix ≡ vReplicate n []
-- transpose-empty-lemma {n = O   } [] = refl
-- transpose-empty-lemma {n = S n'} [] = ≡-congruence ? transpose-empty-lemma {n = n'} []

postulate empty-const-lemma : ∀ {A : Set} {n : ℕ} (degeneratedHorizontalMatrix : Matrix A O n) → is-constant (vMap {n = n} (column degeneratedHorizontalMatrix))

empty-const-lemma' : ∀ {A : Set} {n : ℕ} (degeneratedHorizontalMatrix : Matrix A O n) → is-constant (column degeneratedHorizontalMatrix)
empty-const-lemma' [] _ _ = refl

postulate transpose-prepone-lemma : ∀ {A : Set} {m n : ℕ} (row : Vec A n) (rows : Matrix A m n) → transpose (row ∷ rows) ≡ preponeColumn row (transpose rows)
-- transpose-prepone-lemma [] [] = refl

postulate row-to-column : ∀ {A : Set} {m n : ℕ} (rows : Matrix A m n) (i : Fin m) → rows [ i ] ≡ column (transpose rows) i
-- row-to-column ([]       ∷ rows) fZero = refl
-- row-to-column ((a ∷ []) ∷ rows) fZero = refl
-- row-to-column ((a ∷ as) ∷ []  ) fZero = row-to-column (as ∷ []) fZero

postulate transpose-is-involution : ∀ {A : Set} {m n : ℕ} (rows : Matrix A m n) → transpose (transpose rows) ≡ rows
-- TODO
