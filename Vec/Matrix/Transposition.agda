module Vec.Matrix.Transposition where

open import Vec.Matrix.Base using (Matrix; _[_,_]; matrix-extensionality)
open import Vec.Matrix.RowsAndColumns using ([-]; headColumn; [|]; _:|:_; _[*,_]; access-commutativity; columnal-cons-access-head; columnal-cons-access-tail)
open import Vec.Base using (Vec; []; _∷_; vMap)
open import Vec.Access using (_[_])
open import Vec.Functor using (vMap-functor-keeps-constantness)
open import Nat.Base using (ℕ; O; S)
open import Fin.Base using (Fin; fZero; fSucc)
open import Nat.Notation
open import Fin.Notation
open import Eq using (_≡_; refl; ≡-symmetry; ≡-transitivity; ≡-congruence)



transpose : ∀ {A : Set} {m n : ℕ} → Matrix A m n → Matrix A n m
transpose []           = [|]
transpose (row ∷ rows) = row :|: transpose rows

transpose[|]≡[-] : ∀ {A : Set} {n : ℕ} → transpose [|] ≡ [-] {A} {n}
transpose[|]≡[-] {A} {O}    = refl
transpose[|]≡[-] {A} {S m'} = ≡-congruence ([] :|:_) (transpose[|]≡[-] {A} {m'})

-- The dual is trivial by definition, i.e. same as `refl`:
-- transpose[-]≡[|] : ∀ {A : Set} {m : ℕ} → transpose [-] ≡ [|] {A} {m}

transpose-sample₁ : transpose (   (#0 ∷ #1 ∷ #2 ∷ #3 ∷ []) ∷
                                  (#3 ∷ #2 ∷ #1 ∷ #0 ∷ []) ∷ []
                              )
                              ≡
                                  (#0 ∷ #3 ∷ []) ∷
                                  (#1 ∷ #2 ∷ []) ∷
                                  (#2 ∷ #1 ∷ []) ∷
                                  (#3 ∷ #0 ∷ []) ∷ []
transpose-sample₁ = refl


-- head-row-transpones-to-head-column : ∀ {A : Set} {m n : ℕ} (row : Vec A n) (rows : Matrix A m n) → transpose (row ∷ rows) = consColumn


row-to-column : ∀ {A : Set} {m n : ℕ} (rows⁺ : Matrix A m n) (i : Fin m) → rows⁺ [ i ] ≡ (transpose rows⁺) [*, i ]
row-to-column (row ∷ rows) fZero      = ≡-symmetry (columnal-cons-access-head row (transpose rows))
row-to-column (row ∷ rows) (fSucc i') = ≡-transitivity (row-to-column rows i') (≡-symmetry (columnal-cons-access-tail row (transpose rows) i'))


transposition-swaps-indices : ∀ {A : Set} {m n : ℕ} (mat : Matrix A m n) (i : Fin m) (j : Fin n) → mat [ i , j ] ≡ (transpose mat) [ j , i ]
transposition-swaps-indices mat i j = ≡-transitivity (≡-congruence _[ j ] (row-to-column mat i)) (≡-symmetry (access-commutativity (transpose mat) j i))

double-transposition-keeps-indices : ∀ {A : Set} {m n : ℕ} (mat : Matrix A m n) (i : Fin m) (j : Fin n) → (transpose (transpose mat)) [ i , j ] ≡ mat [ i , j ]
double-transposition-keeps-indices mat i j = ≡-symmetry (≡-transitivity (transposition-swaps-indices mat i j) (transposition-swaps-indices (transpose mat) j i))


transpose-is-involution : ∀ {A : Set} {m n : ℕ} (mat : Matrix A m n) → transpose (transpose mat) ≡ mat
transpose-is-involution mat = matrix-extensionality (transpose (transpose mat)) mat (double-transposition-keeps-indices mat)
