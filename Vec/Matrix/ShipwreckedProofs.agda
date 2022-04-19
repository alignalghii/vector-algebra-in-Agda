module Vec.Matrix.ShipwreckedProofs where

open import Vec.Matrix.Transposition using (transpose)
open import Vec.Matrix.TranspositionAlternative using (transpose')
open import Vec.Matrix.Base using (Matrix; _[_,_])
open import Vec.Matrix.RowsAndColumns using ([-]; headColumn; [|]; _:|:_; _[*,_]; access-commutativity)
open import Vec.Base using (Vec; []; _∷_; vMap)
open import Vec.Access using (_[_])
open import Vec.Functor using (vMap-functor-keeps-constantness)
open import Nat.Base using (ℕ; O; S)
open import Fin.Base using (Fin; fZero; fSucc)
open import Eq using (_≡_; refl; ≡-symmetry; ≡-transitivity; ≡-congruence)
open import CategoricalTheorems using (is-constant)


degenerate-row-to-col  : ∀ {A : Set} {m : ℕ} → transpose  [-] ≡ [|] {A} {m}
degenerate-row-to-col = refl

postulate degenerate-row-to-col' : ∀ {A : Set} {m : ℕ} → transpose' [-] ≡ [|] {A} {m}
-- degenerate-row-to-col' {m = O   } = refl
-- degenerate-row-to-col' {m = S m'} = -- WRONG -- ≡-congruence (_∷ []) degenerate-row-to-col' {m = m'}


empty-const-lemma : ∀ {A : Set} {n : ℕ} → is-constant (vMap {n = n} ([-] {A} {n} [*,_]))
empty-const-lemma = vMap-functor-keeps-constantness ([-] [*,_]) (λ _ _ → refl)

postulate transpose-empty-lemma : ∀ {A : Set} {n : ℕ} → transpose' [-] ≡ [|] {A} {n}
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


postulate transpose-prepone-lemma : ∀ {A : Set} {m n : ℕ} (row : Vec A n) (rows : Matrix A m n) → transpose' (row ∷ rows) ≡ row :|: (transpose' rows)
-- transpose-prepone-lemma [] [] = refl


head' : ∀ {A : Set} {n : ℕ} → Vec A (S n) → A
head' (a ∷ _) = a

-- TODO prove the equivalence of `head` and `head'` in all possible contexts (there were problems about this)

tail' : ∀ {A : Set} {n : ℕ} → Vec A (S n) → A
tail' {n = O}    _   = []
tail' {n = S n'} vec = vMap (vec [_]) (vMap fScucc (seq n'))

-- TODO prove the equivalence of `tail` and `tail'` in all possible contexts (there were problems about this)

