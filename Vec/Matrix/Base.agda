module Vec.Matrix.Base where

open import Vec.Base using (Vec; []; _∷_; vMap; vZipWith; vReplicate; vFillOutWith)
open import Vec.Access using (_[_]; head)
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


_[_,_] : ∀ {A : Set} {m n : ℕ} → Matrix A m n → Fin m → Fin n → A
rows [ i , j ] = rows [ i ] [ j ]

*[*,*]-sample₁ : (   (#0 ∷ #1 ∷ #2 ∷ #3 ∷ []) ∷
                     (#3 ∷ #2 ∷ #1 ∷ #0 ∷ []) ∷ []
                 )
                 [ #1₂ , #2₄ ]
                 ≡
                 #1
*[*,*]-sample₁ = refl
