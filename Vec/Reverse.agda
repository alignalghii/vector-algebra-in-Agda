module Vec.Reverse where

open import Vec.Base using (Vec; []; _∷_; _++_; last)
open import Nat.Base using (ℕ; O; S; _+_; +-has-left-neutral; +-is-left-recurrible; +-commutativity)
open import Eq using (_≡_; refl; ≡-symmetry; ≡-transitivity; ≡-transitivity₃; ≡-congruence; subst)
open import Combinators using (flip)


infix 6 _+'_
_+'_ : ℕ → ℕ → ℕ
O   +' n = n         -- +' has left-neutral
S m +' n = m +' S n

+'-is-left-recurrible : ∀ (m n : ℕ) → S m +' n ≡ S (m +' n)
+'-is-left-recurrible O     n = refl
+'-is-left-recurrible (S m) n = +'-is-left-recurrible m (S n)

+'-is-right-recurrible : ∀ (m n : ℕ) → m +' S n ≡ S (m +' n)
+'-is-right-recurrible O     n = refl
+'-is-right-recurrible (S m) n = +'-is-right-recurrible m (S n)

+'-has-right-neutral : ∀ (m : ℕ) → m +' O ≡ m
+'-has-right-neutral O      = refl
+'-has-right-neutral (S m') = ≡-transitivity (+'-is-right-recurrible m' O) (≡-congruence S (+'-has-right-neutral m')) 

+'≡+ : ∀ (m n : ℕ) → m +' n ≡ m + n
+'≡+ O     n = ≡-symmetry (+-has-left-neutral n)
+'≡+ (S m) n = ≡-transitivity₃ (+'-is-left-recurrible m n) (≡-congruence S (+'≡+ m n)) (≡-symmetry (+-is-left-recurrible m n))

stack-onto' : ∀ {A : Set} {m n : ℕ} → Vec A m → Vec A n → Vec A (m +' n)
stack-onto' []       stack = stack
stack-onto' (a ∷ as) stack = stack-onto' as (a ∷ stack)

reverse' : ∀ {A : Set} {m : ℕ} → Vec A m → Vec A (m +' O)
reverse' = flip stack-onto' []

-----------------------------------------------------------
-- For solving the casting problem, credit to
--    - Dominique Devriese in reply to Lyndon Maydwell on Agda maillist: [Problem with reversing vector](https://lists.chalmers.se/pipermail/agda/2012/004097.html)
--    - Philip Wadler & Wen Kokke & Jeremy G. Siek: PLFA, [substitution](https://plfa.github.io/Equality/#cong)
-----------------------------------------------------------

stack-onto : ∀ {A : Set} {m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
stack-onto {A} {m} {n} v stack = subst (Vec A) (+'≡+ m n) (stack-onto' v stack)
-- subst (Vec A) (≡-transitivity (+'≡+ m n) (+-commutativity m n)) (stack-onto' v stack)

reverse : ∀ {A : Set} {m : ℕ} → Vec A m → Vec A m
reverse = flip stack-onto []
-- reverse {A} {m} v = subst (Vec A) (+'≡+ m O) (reverse' v)

-- conv : ∀ {A : Set} {n : ℕ} → Vec A n → Vec A (O + n)
-- conv v = v ++ []

-- convert : ∀ {A : Set} {m : ℕ} → Vec A m → Vec A (m +' O)
-- convert [] = []
-- convert (a ∷ as) = convert as

stack-onto'-has-left-neutral : ∀ {A : Set} {n : ℕ} (stack : Vec A n) → stack-onto' [] stack ≡ stack
stack-onto'-has-left-neutral stack = refl

postulate stack-onto'-keeps-preexistent-stack-bottom : ∀ {A : Set} {m n : ℕ} (v : Vec A m) (neStack : Vec A (S n)) → last (stack-onto' v neStack) ≡ last neStack

postulate stack-onto-has-left-neutral : ∀ {A : Set} {n : ℕ} (stack : Vec A n) → subst (Vec A) (+-has-left-neutral n) (stack-onto [] stack) ≡ stack
--stack-onto-has-left-neutral [] = refl
--stack-onto-has-left-neutral (s ∷ ss) = refl

postulate stack-onto-keeps-preexistent-stack-bottom : ∀ {A : Set} {m n : ℕ} (v : Vec A m) (neStack : Vec A (S n)) → last (stack-onto v neStack) ≡ last neStack 
-- stack-onto-keeps-preexistent-stack-bottom {.A} {.O} {.n} [] neStack = refl
-- subst (Vec A) (+-has-left-neutral (S n)) (stack-onto [] neStack)

postulate head-goes-last-in-reverse : ∀ {A : Set} {n : ℕ} {a : A} {as : Vec A n} → last (a ∷ as) ≡ a
-- head-goes-last-in-reverse {A} {O  } {a} {[]} = refl
-- head-goes-last-in-reverse {A} {S n} {a} {as} = refl

postulate reverse-is-involutive : ∀ {A : Set} {n : ℕ} (v : Vec A n) → reverse (reverse v) ≡ v
-- reverse-is-involutive []       = refl
-- reverse-is-involutive (a ∷ as) = ? (reverse-is-involutive as)
