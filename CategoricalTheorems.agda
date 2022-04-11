module CategoricalTheorems where

open import Eq using (_≡_; refl)
open import Combinators using (_∘_)


is-constant : ∀ {A B : Set} → (A → B) → Set
is-constant {A} f = ∀ (a₁ a₂ : A) → f a₁ ≡ f a₂

const-precompose : ∀ {A B : Set} (f : A → B) (g : A → A) → is-constant f → ∀ (a : A) → (f ∘ g) a ≡ f a
const-precompose f g f-constantness a = f-constantness (g a) a
