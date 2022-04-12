module CategoricalTheorems where

open import Eq using (_≡_; refl)
open import Combinators using (_∘_)


is-constant : ∀ {A B : Set} → (A → B) → Set
is-constant {A} f = ∀ (a₁ a₂ : A) → f a₁ ≡ f a₂

-- The above `is-constant` is defineable also in a pure categorical language:
-- `f : B → C` is regarded a constant-function, iff ∀ (g₁ g₂ : A → B) → f ∘ g₁ ≡ f ∘ g₂
-- But Agda lacks function extensionality, thus we cannot do that this way.

const-precompose : ∀ {A B : Set} (f : A → B) (g : A → A) → is-constant f → ∀ (a : A) → (f ∘ g) a ≡ f a
const-precompose f g f-constantness a = f-constantness (g a) a
