module Vec.Functor where

open import Vec.Base using (Vec; []; _∷_; vMap)
open import Nat.Base using (ℕ; O; S)
open import Eq using (_≡_; refl; ≡-congruence; ≡-congruence₂)
open import Combinators using (id; _∘_)
open import CategoricalTheorems using (is-constant)


vMap-functor-identity : ∀ {A : Set} {n : ℕ} (as : Vec A n) → vMap id as ≡ id as
vMap-functor-identity [] = refl
vMap-functor-identity (a ∷ as) = (≡-congruence (a ∷_)) (vMap-functor-identity as)

vMap-functor-composition : ∀ {A B C : Set} {n : ℕ} (f : B → C) (g : A → B) (as : Vec A n) → vMap (f ∘ g) as ≡ (vMap f ∘ vMap g) as
vMap-functor-composition _ _ []       = refl
vMap-functor-composition f g (a ∷ as) = ≡-congruence (f (g a) ∷_) (vMap-functor-composition f g as)


vMap-functor-keeps-constantness : ∀ {A B : Set} {n : ℕ} (f : A → B) → is-constant f → is-constant {Vec A n} (vMap f)
vMap-functor-keeps-constantness _ _             []         []         = refl
vMap-functor-keeps-constantness {A} {B} f f-is-constant (a₁ ∷ as₁) (a₂ ∷ as₂) = ≡-congruence₂ {A} {B} (_∷_) (f-is-constant a₁ a₂) (vMap-functor-keeps-constantness f f-is-constant as₁ as₂)

-- In category theory, we would do the above proof more ecomomically:
--- usingthe functor rules only (and probably needed also some additional rules, but those also being in pure categorcal language)
--
-- Remember, the category theory definition of being a contant function is:
-- `f : B → C` is regarded a constant-function, iff ∀ (g₁ g₂ : A → B) → f ∘ g₁ ≡ f ∘ g₂
--
-- But in Agda, the proof probably cannot be done using only the functor rules,
-- (i.e. in the pure categorical way),
-- because Agda lacks function extensionality (funExt).
-- Thus we have to use the specific `vMap` functor directly for the proof, as shown above.
--
-- TODO: for funExt, learn homotopy type theory and Cubical
-- https://agda.readthedocs.io/en/v2.6.2.1/language/cubical.html#the-interval-and-path-types


-- Pure man's funExt: let us prove specific extensionality lemmas for possbile contexts where it turns out to be needed in the actual task:

vMap-extensionality : ∀ {A B : Set} (f₁ f₂ : A → B) → (∀ (a : A) → f₁ a ≡ f₂ a) → (∀ {n : ℕ} (v : Vec A n) → vMap f₁ v ≡ vMap f₂ v)
vMap-extensionality         _  _  _     {O}    []       = refl
vMap-extensionality {A} {B} f₁ f₂ f₁≡f₂ {S n'} (a ∷ as) = ≡-congruence₂ {A} {B} _∷_ (f₁≡f₂ a) (vMap-extensionality f₁ f₂ f₁≡f₂ as)
