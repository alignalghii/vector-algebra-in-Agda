module Eq where

open import Combinators using (flipped-app)


-- Datatype

infix 4 _≡_
data _≡_ {A : Set} (a : A) : A → Set where
    refl : a ≡ a


-- Basic rules:

≡-symmetry : ∀ {A : Set} {a₁ a₂ : A} → a₁ ≡ a₂ → a₂ ≡ a₁
≡-symmetry refl = refl

≡-transitivity : ∀ {A : Set} {a₁ a₂ a₃ : A} → a₁ ≡ a₂ → a₂ ≡ a₃ → a₁ ≡ a₃
≡-transitivity refl refl = refl

≡-transitivity₃ : ∀ {A : Set} {a₁ a₂ a₃ a₄ : A} → a₁ ≡ a₂ → a₂ ≡ a₃ → a₃ ≡ a₄ → a₁ ≡ a₄
≡-transitivity₃ refl refl refl = refl

≡-congruence : ∀ {A B : Set} (f : A → B) {a₁ a₂ : A} → a₁ ≡ a₂ → f a₁ ≡ f a₂
≡-congruence f refl = refl

subst : ∀ {A : Set} {a a' : A} (P : A → Set) → a ≡ a' → P a → P a'
subst P refl pa = pa


-- Derived rules:

≡-congruence-flipped-app : ∀ {A B : Set} {f₁ f₂ : A → B} → f₁ ≡ f₂ → (a : A)  → f₁ a ≡ f₂ a
≡-congruence-flipped-app f₁≡f₂ a = ≡-congruence (flipped-app a) f₁≡f₂

≡-congruence-around-app : ∀ {A B : Set} {f₁ f₂ : A → B} {a₁ a₂ : A} → f₁ ≡ f₂ → a₁ ≡ a₂ → f₁ a₁ ≡ f₂ a₂
≡-congruence-around-app {f₁ = f₁} {a₂ = a₂} f₁≡f₂ a₁≡a₂ = ≡-transitivity (≡-congruence f₁ a₁≡a₂) (≡-congruence-flipped-app f₁≡f₂ a₂)

≡-congruence₂ : ∀ {A B C : Set} {A B : Set} {a₁ a₂ : A} {b₁ b₂ : B} (f : A → B → C) → a₁ ≡ a₂ → b₁ ≡ b₂ → f a₁ b₁ ≡ f a₂ b₂
≡-congruence₂ f a₁≡a₂ b₁≡b₂ = ≡-congruence-around-app (≡-congruence f a₁≡a₂) b₁≡b₂


-- Impossible rules:

-- ≡-extensionality : ∀ {A B : Set} (f₁ f₂ : A → B) → (∀ (a : A) → f₁ a ≡ f₂ a) → f₁ ≡ f₂
-- ≡-extensionality {A} {B} f₁ f₂ p = refl {A → B} {f₁} {f₂}
