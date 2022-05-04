module Vec.Seq where

open import Vec.Base
open import Vec.Access
open import Vec.Functor using (vMap-functor-identity; vMap-functor-composition)
open import Nat.Base
open import Fin.Base
open import Nat.Notation
open import Fin.Notation
open import Logic.Eq
open import Logic.Combinators using (id; _∘_)


Seq : ℕ → Set
Seq n = Vec (Fin n) n

seq : ∀ (n : ℕ) → Seq n
seq O = []
seq (S n) = fZero ∷ vMap fSucc (seq n)

seq-sample₁ : seq #4 ≡ #0₄ ∷ #1₄ ∷ #2₄ ∷ #3₄ ∷ []
seq-sample₁ = refl

seq-mapping-application : ∀ {A : Set} {n : ℕ} (f : Fin n → A) (i : Fin n) → vMap f (seq n) [ i ] ≡ f i
seq-mapping-application            _ fZero      = refl
seq-mapping-application {n = S n'} f (fSucc i') = ≡-transitivity
                                                  (
                                                      ≡-congruence (_[ i' ] )
                                                      (
                                                          ≡-symmetry
                                                          (vMap-functor-composition f fSucc (seq n'))
                                                      )
                                                  )
                                                  (seq-mapping-application (f ∘ fSucc) i')

seq-indexing-identity : ∀ {n : ℕ} (i : Fin n) → (seq n) [ i ] ≡ i
seq-indexing-identity {n} i = ≡-transitivity
                              (
                                  ≡-symmetry
                                  (
                                      ≡-congruence (_[ i ])
                                      (vMap-functor-identity (seq n))
                                  )
                              )
                              (seq-mapping-application id i)
