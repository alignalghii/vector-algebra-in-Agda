module Vec.Functor where

open import Vec.Base using (Vec; []; _∷_; vMap)
open import Nat.Base using (ℕ)
open import Eq using (_≡_; refl; ≡-congruence)
open import Combinators using (id; _∘_)


vMap-functor-identity : ∀ {A : Set} {n : ℕ} (as : Vec A n) → vMap id as ≡ id as
vMap-functor-identity [] = refl
vMap-functor-identity (a ∷ as) = (≡-congruence (a ∷_)) (vMap-functor-identity as)

vMap-functor-composition : ∀ {A B C : Set} {n : ℕ} (f : B → C) (g : A → B) (as : Vec A n) → vMap (f ∘ g) as ≡ (vMap f ∘ vMap g) as
vMap-functor-composition _ _ []       = refl
vMap-functor-composition f g (a ∷ as) = ≡-congruence (f (g a) ∷_) (vMap-functor-composition f g as)
