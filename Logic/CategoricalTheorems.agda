module Logic.CategoricalTheorems where

open import Logic.Eq using (_≡_; refl)
open import Logic.Combinators using (_∘_)


is-constant : ∀ {A B : Set} → (A → B) → Set
is-constant {A} f = ∀ (a₁ a₂ : A) → f a₁ ≡ f a₂

-- The above `is-constant` is defineable also in a pure categorical language:
-- `f : B → C` is regarded a constant-function, iff ∀ (g₁ g₂ : A → B) → f ∘ g₁ ≡ f ∘ g₂
-- But Agda lacks function extensionality (funExt), thus we cannot do that this way.
--
-- TODO: for funExt, learn homotopy type theory and Cubical
-- https://agda.readthedocs.io/en/v2.6.2.1/language/cubical.html#the-interval-and-path-types

const-precompose : ∀ {A B : Set} (f : A → B) (g : A → A) → is-constant f → ∀ (a : A) → (f ∘ g) a ≡ f a
const-precompose f g f-constantness a = f-constantness (g a) a
