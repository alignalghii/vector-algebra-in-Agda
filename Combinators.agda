module Combinators where


const : ∀ {A B : Set} → A → B → A
const a _ = a

id : ∀ {A : Set} → A → A
id a = a

flip : ∀ {A B C : Set} → (A → B → C) → (B → A → C)
flip f b a = f a b

infixr 9 _∘_
_∘_ : ∀ {A : Set} {B : A → Set} {C : ∀ (a : A) → B a → Set} (f : ∀ {a : A} (b : B a) → C a b) (g : ∀ (a : A) → B a)  → ∀ (a : A) → C a (g a)
(f ∘ g) a = f (g a)

flipped-app : ∀ {A B : Set} → A → (A → B) → B
flipped-app = flip id
