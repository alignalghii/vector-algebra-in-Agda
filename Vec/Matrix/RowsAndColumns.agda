module Vec.Matrix.RowsAndColumns where

open import Vec.Matrix.Base using (Matrix)
open import Vec.Base using (Vec; []; _∷_; vMap; vZipWith; vFillOutWith)
open import Vec.Access using (_[_]; head; tail; vExtensionality)
open import Nat.Base using (ℕ; O; S)
open import Fin.Base using (Fin; fZero; fSucc)
open import Eq using (_≡_; refl; ≡-congruence)


columnAt _[*,_] : ∀ {A : Set} {m n : ℕ} → Matrix A m n → Fin n → Vec A m
columnAt rows j = vMap _[ j ] rows
_[*,_] = columnAt

headColumn : ∀ {A : Set} {m n : ℕ} (rows : Matrix A m (S n)) → Vec A m
headColumn = vMap head

consColumn _:|:_ : ∀ {A : Set} {m n : ℕ} → Vec A m → Matrix A m n → Matrix A m (S n)
consColumn column₀ columns = vZipWith (_∷_) column₀ columns
_:|:_ = consColumn

nilColumn [|] : ∀ {A : Set} {m : ℕ} → Matrix A m O
nilColumn = vFillOutWith []
[|] = nilColumn

column-tail : ∀ {A : Set} {m n : ℕ} → Matrix A m (S n) → Matrix A m n
column-tail = vMap tail

degeneratedHorizontalMatrix [-] : ∀ {A : Set} {n : ℕ} → Matrix A O n
degeneratedHorizontalMatrix = []
[-] = degeneratedHorizontalMatrix

access-commutativity : ∀ {A : Set} {m n : ℕ} (rows : Matrix A m n) (i : Fin m) (j : Fin n) → rows [ i ] [ j ] ≡ rows [*, j ] [ i ]
access-commutativity {m = O   } []           ()          _
access-commutativity {m = S m'} (row ∷ rows) fZero       j = refl
access-commutativity {m = S m'} (row ∷ rows) (fSucc i')  j = access-commutativity rows i' j

-- Columnal access theorems:

columnal-cons-access-head : ∀ {A : Set} {m n : ℕ} (col : Vec A m) (rows : Matrix A m n) → (col :|: rows) [*, fZero ]   ≡ col
columnal-cons-access-head []       []           = refl
columnal-cons-access-head (a₀₀ ∷ a₊₀) (_ ∷ a₊₊) = ≡-congruence (a₀₀ ∷_) (columnal-cons-access-head a₊₀ a₊₊)

columnal-cons-access-tail : ∀ {A : Set} {m n : ℕ} (col : Vec A m) (rows : Matrix A m n) (i : Fin n) → (col :|: rows) [*, fSucc i ] ≡ rows [*, i ]
columnal-cons-access-tail []          []          _ = refl
columnal-cons-access-tail (a₀₀ ∷ a₊₀) (a₀₊ ∷ a₊₊) i = ≡-congruence (a₀₊ [ i ] ∷_) (columnal-cons-access-tail a₊₀ a₊₊ i)
