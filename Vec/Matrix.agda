module Vec.Matrix where

open import Vec.Base using (Vec; []; _∷_; vMap; vZipWith; vReplicate; vFillOutWith)
open import Vec.Access using (_[_]; head; vExtensionality)
open import Vec.Functor using (vMap-functor-keeps-constantness)
open import Nat.Base using (ℕ; O; S)
open import Nat.Notation using (#0; #1; #2; #3)
open import Fin.Base using (Fin; fZero; fSucc)
open import Fin.Notation using (#1₂; #2₄)
open import Vec.Seq using (seq)
open import Eq using (_≡_; refl; ≡-symmetry; ≡-transitivity; ≡-congruence)
open import CategoricalTheorems using (is-constant)


Matrix : Set → ℕ → ℕ → Set
Matrix = λ A m n → Vec (Vec A n) m


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
transpose []           = vFillOutWith []
transpose (row ∷ rows) = consColumn row (transpose rows)

transpose-sample₁ : transpose (   (#0 ∷ #1 ∷ #2 ∷ #3 ∷ []) ∷
                                  (#3 ∷ #2 ∷ #1 ∷ #0 ∷ []) ∷ []
                              )
                              ≡
                                  (#0 ∷ #3 ∷ []) ∷
                                  (#1 ∷ #2 ∷ []) ∷
                                  (#2 ∷ #1 ∷ []) ∷
                                  (#3 ∷ #0 ∷ []) ∷ []
transpose-sample₁ = refl


empty-const-lemma : ∀ {A : Set} {n : ℕ} (degeneratedHorizontalMatrix : Matrix A O n) → is-constant (vMap {n = n} (columnAt degeneratedHorizontalMatrix))
empty-const-lemma [] = vMap-functor-keeps-constantness (columnAt []) (λ _ _ → refl)

postulate transpose-empty-lemma : ∀ {A : Set} {n : ℕ} (degeneratedHorizontalMatrix : Matrix A O n) → transpose degeneratedHorizontalMatrix ≡ vReplicate n []
-- transpose-empty-lemma {n = O   } [] = refl
-- transpose-empty-lemma {n = S n'} [] = ≡-congruence ([] ∷_)
--                                      (
--                                           ≡-transitivity
--                                           (
--                                                  (
--                                                       empty-const-lemma []
--                                                       (vMap fSucc (seq n'))
--                                                       (seq n')
--                                                  )
--                                           )
--                                           (transpose-empty-lemma {n = n'} [])
--                                      )


postulate transpose-prepone-lemma : ∀ {A : Set} {m n : ℕ} (row : Vec A n) (rows : Matrix A m n) → transpose (row ∷ rows) ≡ consColumn row (transpose rows)
-- transpose-prepone-lemma [] [] = refl

column-head-cons-identity : ∀ {A : Set} {m n : ℕ} (column₀ : Vec A m) (rows : Matrix A m n) → headColumn (consColumn column₀ rows) ≡ column₀
column-head-cons-identity []              []                      = refl
column-head-cons-identity (a₀₀ ∷ a₊₀) (a₀₊ ∷ a₊₊) = ≡-congruence (a₀₀ ∷_) (column-head-cons-identity a₊₀ a₊₊)

column-at-cons-tail-identity : ∀ {A : Set} {m n : ℕ} (column₀ : Vec A m) (row⁺s : Matrix A m n) (i : Fin n) → columnAt (consColumn column₀ row⁺s) (fSucc i) ≡ columnAt row⁺s i
column-at-cons-tail-identity []          []          i = refl
column-at-cons-tail-identity (a₀₀ ∷ a₊₀) (a₀₊ ∷ a₊₊) i = ≡-congruence (a₀₊ [ i ] ∷_) (column-at-cons-tail-identity a₊₀ a₊₊ i)

-- head-row-transpones-to-head-column : ∀ {A : Set} {m n : ℕ} (row : Vec A n) (rows : Matrix A m n) → transpose (row ∷ rows) = consColumn


row-to-column : ∀ {A : Set} {m n : ℕ} (rows⁺ : Matrix A m n) (i : Fin m) → rows⁺ [ i ] ≡ columnAt (transpose rows⁺) i
row-to-column (row ∷ rows) fZero      = ≡-symmetry (column-head-cons-identity row (transpose rows))
row-to-column (row ∷ rows) (fSucc i') = ≡-transitivity (row-to-column rows i') (≡-symmetry (column-at-cons-tail-identity row (transpose rows) i'))

access-commutativity : ∀ {A : Set} {m n : ℕ} (rows : Matrix A m n) (i : Fin m) (j : Fin n) → rows [ i ] [ j ] ≡ rows [*, j ] [ i ]
access-commutativity {m = O   } []           ()          _
access-commutativity {m = S m'} (row ∷ rows) fZero       j = refl
access-commutativity {m = S m'} (row ∷ rows) (fSucc i')  j = access-commutativity rows i' j

-- ? -- row-to-column rows i -- ≡-symmetry (column-head-cons-identity row (transpose rows))
-- row-to-column ((a ∷ []) ∷ []) fZero = refl
-- row-to-column ((a ∷ []) ∷ rows) fZero = refl
-- row-to-column ((a ∷ as) ∷ []  ) fZero = row-to-column (as ∷ []) fZero

transposition-swaps-indices : ∀ {A : Set} {m n : ℕ} (mat : Matrix A m n) (i : Fin m) (j : Fin n) → mat [ i , j ] ≡ (transpose mat) [ j , i ]
transposition-swaps-indices mat i j = ≡-transitivity (≡-congruence _[ j ] (row-to-column mat i)) (≡-symmetry (access-commutativity (transpose mat) j i))

double-transposition-keeps-indices : ∀ {A : Set} {m n : ℕ} (mat : Matrix A m n) (i : Fin m) (j : Fin n) → (transpose (transpose mat)) [ i , j ] ≡ mat [ i , j ]
double-transposition-keeps-indices mat i j = ≡-symmetry (≡-transitivity (transposition-swaps-indices mat i j) (transposition-swaps-indices (transpose mat) j i))

matrix-extensionality : ∀ {A : Set} {m n : ℕ} (mat₁ mat₂ : Matrix A m n) → (∀ (i : Fin m) (j : Fin n) → mat₁ [ i ] [ j ] ≡ mat₂ [ i ] [ j ]) → mat₁ ≡ mat₂
matrix-extensionality mat₁ mat₂ extEq = vExtensionality mat₁ mat₂ (λ i → vExtensionality (mat₁ [ i ]) (mat₂ [ i ]) (extEq i))

transpose-is-involution : ∀ {A : Set} {m n : ℕ} (mat : Matrix A m n) → transpose (transpose mat) ≡ mat
transpose-is-involution mat = matrix-extensionality (transpose (transpose mat)) mat (double-transposition-keeps-indices mat)
