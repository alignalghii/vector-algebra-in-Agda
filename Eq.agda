module Eq where


infix 4 _≡_
data _≡_ {A : Set} (a : A) : A → Set where
    refl : a ≡ a

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
