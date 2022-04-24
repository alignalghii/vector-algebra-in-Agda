module Vec.Matrix.TranspositionAlternative where

open import Vec.Matrix.Base using (Matrix)
open import Vec.Matrix.Transposition using (transpose; transpose[|]≡[-])
open import Vec.Matrix.RowsAndColumns using (_[*,_]; [|]; [-]; _:|:_; column-tail; columnal-cons-access-head; columnal-cons-access-tail)
open import Vec.Base using (Vec; []; _∷_; vMap)
open import Vec.Functor using (vMap-functor-composition; vMap-extensionality)
open import Vec.Seq using (seq)
open import Nat.Base using (ℕ; O ; S)
open import Fin.Base using (Fin; fZero; fSucc)
open import Eq using (_≡_; refl; ≡-symmetry; ≡-transitivity; ≡-congruence)
open import Combinators using (const; _∘_)


co-transpose : ∀ {A : Set} {m n : ℕ} → Matrix A m n → Matrix A n m
co-transpose {n = n} mat = vMap (mat [*,_]) (seq n)

test4 : ∀ {A : Set} {m : ℕ} → vMap (([-] {A} {S m} [*,_]) ∘ fSucc) (seq m) ≡ co-transpose ([-] {A} {m}) -- vMap (([-] {A} {m}) [*,_]) (seq m)
test4 {A} {m} = vMap-extensionality (([-] {A} {S m} [*,_]) ∘ fSucc) (([-] {A} {m}) [*,_]) (const refl) (seq m)

-- test5 : ∀ {A : Set} {m : ℕ} → (vMap (([-] {A} {S m}) [*,_]) ∘ vMap fSucc) (seq m) ≡ co-transpose ([-] {A} {m}) -- vMap (([-] {A} {m}) [*,_]) (seq m)
-- test5 {A} {m} = ≡-transitivity (≡-symmetry (vMap-functor-composition (([-] {A} {S m}) [*,_]) fSucc (seq m))) test4

-- test6 : ∀ {A : Set} {m : ℕ} → vMap (([-] {A} {S m}) [*,_]) (vMap fSucc (seq m)) ≡ co-transpose ([-] {A} {m}) -- vMap (([-] {A} {m}) [*,_]) (seq m)
-- test6 {A} {m} = ≡-transitivity (≡-symmetry (vMap-functor-composition (([-] {A} {S m}) [*,_]) fSucc (seq m))) test4

test7 : ∀ {A : Set} {m : ℕ} → vMap (([-] {A} {S m}) [*,_]) (vMap fSucc (seq m)) ≡ vMap (([-] {A} {m}) [*,_]) (seq m)
test7 {A} {m} = ≡-transitivity (≡-symmetry (vMap-functor-composition (([-] {A} {S m}) [*,_]) fSucc (seq m))) test4

-- test8 : ∀ {A : Set} {m : ℕ} → [] ∷ vMap (([-] {A} {S m}) [*,_]) (vMap fSucc (seq m)) ≡ [] ∷ vMap (([-] {A} {m}) [*,_]) (seq m)
-- test8 {A} {m} = ≡-congruence ([] ∷_) test7

-- test9 : ∀ {A : Set} {m : ℕ} → vMap (([-] {A} {S m}) [*,_]) (fZero ∷ vMap fSucc (seq m)) ≡ [] ∷ vMap (([-] {A} {m}) [*,_]) (seq m)
-- test9 {A} {m} = ≡-congruence ([] ∷_) test7

test10 : ∀ {A : Set} {m : ℕ} → vMap (([-] {A} {S m}) [*,_]) (seq (S m)) ≡ [] ∷ vMap (([-] {A} {m}) [*,_]) (seq m)
test10 {A} {m} = ≡-congruence ([] ∷_) test7

cotransposition-empty-shifting : ∀ {A : Set} {m : ℕ} → co-transpose ([-] {A} {S m}) ≡ [] ∷ co-transpose ([-] {A} {m})
cotransposition-empty-shifting {A} {m} = ≡-congruence ([] ∷_) test7

cotranspose[-]≡[|] : ∀ {A : Set} {m : ℕ} → co-transpose [-] ≡ [|] {A} {m}
cotranspose[-]≡[|] {A} {m = O}    = refl
cotranspose[-]≡[|] {A} {m = S m'} = ≡-transitivity cotransposition-empty-shifting ((≡-congruence ([] ∷_) (cotranspose[-]≡[|] {A} {m'})))

-- ? -- ≡-congruence ([-] :|:_) (row-nil-cotransposes-to-column-nil {A} {m'})
-- Maybe this theorem shoould not be stated on its owns
-- as it is no easier (is even harder) than the general transposition-has-equivalent-alternative-definitions

-- The dual is trivial by definition, i.e. same as `refl`:
-- cotranspose[|]≡[-] : ∀ {A : Set} {n : ℕ} → co-transpose [|] ≡ [-] {A} {n}

transposition-has-equivalent-alternative-definitions : ∀ {A : Set} {m n : ℕ} (mat : Matrix A m n) → transpose mat ≡ co-transpose mat
transposition-has-equivalent-alternative-definitions {m = O}    []       = ≡-symmetry cotranspose[-]≡[|]
transposition-has-equivalent-alternative-definitions {m = S m'} (a ∷ as) = ?

-- To prove this, try to fix and use `Vec/Matrix/ShipwreckedProofs`
