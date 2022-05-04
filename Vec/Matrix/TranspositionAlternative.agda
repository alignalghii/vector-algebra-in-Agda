module Vec.Matrix.TranspositionAlternative where

open import Vec.Matrix.Base using (Matrix)
open import Vec.Matrix.Transposition using (transpose; transpose[|]≡[-]; transposition-swaps-indices)
open import Vec.Matrix.Extensionality using (matrix-extensionality)
open import Vec.Matrix.Involution using (Index-swapping)
open import Vec.Matrix.RowsAndColumns using (_[*,_]; [|]; [-]; _:|:_; column-tail; columnal-cons-access-head; columnal-cons-access-tail; access-commutativity)
open import Vec.Base using (Vec; []; _∷_; vMap)
open import Vec.Access using (_[_])
open import Vec.Functor using (vMap-functor-composition; vMap-extensionality)
open import Vec.Seq using (seq; seq-mapping-application)
open import Nat.Base using (ℕ; O ; S)
open import Fin.Base using (Fin; fZero; fSucc)
open import Logic.Eq using (_≡_; refl; ≡-symmetry; ≡-transitivity; ≡-congruence; ≡-congruence₂)
open import Logic.Combinators using (const; _∘_)


co-transpose : ∀ {A : Set} {m n : ℕ} → Matrix A m n → Matrix A n m
co-transpose {n = n} mat = vMap (mat [*,_]) (seq n)

cotransposition-column-to-row : ∀ {A : Set} {m n : ℕ} (mat : Matrix A m n) (j : Fin n) → (co-transpose mat) [ j ] ≡ mat [*, j ]
cotransposition-column-to-row mat j = seq-mapping-application (mat [*,_]) j

-- @TODO: generalize and factor out to `Vec.Matrix.Involution`
cotransposition-swaps-indices : ∀ {A : Set} {m n : ℕ} → Index-swapping {A} {m} {n} co-transpose
cotransposition-swaps-indices {A} {m} {n} mat i j = ≡-transitivity
                                                    (access-commutativity mat i j)
                                                    (
                                                        ≡-congruence _[ i ]
                                                        (
                                                            ≡-symmetry
                                                            (cotransposition-column-to-row mat j)
                                                        )
                                                    )

-- Transposition has equivalent alternative definitions:

transposition≡cotransposition : ∀ {A : Set} {m n : ℕ} (mat : Matrix A m n) → transpose mat ≡ co-transpose mat
transposition≡cotransposition mat = matrix-extensionality (transpose mat) (co-transpose mat)
                                    (
                                        λ i j → ≡-transitivity
                                                (
                                                    ≡-symmetry
                                                    (transposition-swaps-indices mat j i)
                                                )
                                                (cotransposition-swaps-indices mat j i)
                                    )


-------------------------------------------------------------
-- Probably obsolete definitions, but consider, maybe useful
-- confer with also `Vec/Matrix/ShipwreckedProofs`
------------------------------------------------------------

-- Columnal inductivity:

-- cotransposition-columnal-inductivity-base : ∀ {A : Set} {m : ℕ} → co-transpose ([|] {A} {m}) = [-] {A} {m}
-- this simply amounts to `refl`, no need to state expicitly

cotransposition-columnal-inductivity-step : ∀ {A : Set} {m n : ℕ} (col : Vec A m) (rows : Matrix A m n) → co-transpose (col :|: rows) ≡ col ∷ co-transpose rows
cotransposition-columnal-inductivity-step {A} {m} {n} col rows = ≡-congruence₂ {Vec A m} {Matrix A m n} _∷_
                                                                 (columnal-cons-access-head col rows)
                                                                 (
                                                                       ≡-transitivity
                                                                      (
                                                                          ≡-symmetry
                                                                          (
                                                                              vMap-functor-composition
                                                                              ((col :|: rows) [*,_])
                                                                              fSucc
                                                                              (seq n)
                                                                          )
                                                                      )
                                                                      (
                                                                          vMap-extensionality
                                                                          (((col :|: rows) [*,_]) ∘ fSucc)
                                                                          (rows [*,_])
                                                                          (columnal-cons-access-tail col rows)
                                                                          (seq n)
                                                                      )
                                                                 )


cotranspose[-]≡[|] : ∀ {A : Set} {m : ℕ} → co-transpose [-] ≡ [|] {A} {m}
cotranspose[-]≡[|] {A} {m = O}    = refl
cotranspose[-]≡[|] {A} {m = S m'} = ≡-transitivity
                                    (cotransposition-columnal-inductivity-step [] [-])
                                    (
                                        (
                                            ≡-congruence ([] ∷_)
                                            (cotranspose[-]≡[|] {A} {m'})
                                        )
                                    )

-- Maybe this theorem should not be stated on its owns
-- as it is no easier (is even harder) than the general transposition-has-equivalent-alternative-definitions

-- The dual is trivial by definition, i.e. same as `refl`:
-- cotranspose[|]≡[-] : ∀ {A : Set} {n : ℕ} → co-transpose [|] ≡ [-] {A} {n}
