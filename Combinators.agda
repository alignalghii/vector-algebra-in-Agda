module Combinators where


const : ∀ {A B : Set} → A → B → A
const a _ = a

flip : ∀ {A B C : Set} → (A → B → C) → (B → A → C)
flip f b a = f a b
