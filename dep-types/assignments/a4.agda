module a4 where

open import Data.Nat
open import Data.Vec

ind-Vec
  : ∀ {ℓ} {E : Set ℓ} n (v : Vec E n)
  → (motive : ∀ k → Vec E k → Set)
  → motive zero []
  → (∀ k e es → motive k es → motive (suc k) (e ∷ es))
  → motive n v
ind-Vec _ [] motive base step = base
ind-Vec _ (x ∷ v) motive base step = step _ x v (ind-Vec _ v motive base step)


min : ℕ → ℕ → ℕ
min = _⊓_

min-List : ∀ n → Vec ℕ (suc n) → ℕ
min-List n v = ind-Vec n (tail v) (λ { k x → ℕ }) (head v) λ { _ e _ x → min e x }

map-Vec : (A B : Set) → (n : ℕ) → (A → B) → Vec A n → Vec B n
map-Vec A B n f v = ind-Vec n v (λ k _ → Vec B k) [] (λ k e es v → _∷_ (f e) v)

zip-with-Vec : (A B C : Set) → (n : ℕ) → (A → B → C) → Vec A n → Vec B n → Vec C n
zip-with-Vec A B C n f as =
  ind-Vec n as (λ k vs → Vec B k → Vec C k) (λ _ → []) (λ { k a as fbc bs → f a (head bs) ∷ fbc (tail bs) })

snoc-Vec : (E : Set) → (n : ℕ) → Vec E n → E → Vec E (suc n)
snoc-Vec E n v b = ind-Vec n v (λ { k x → Vec E (suc k) }) (b ∷ []) λ { _ e _ x → e ∷ x }

open import Data.List

vec->list : (E : Set) → (n : ℕ) → Vec E n → List E
vec->list E n v = ind-Vec n v (λ _ _ → List E) [] λ { _ e _ x → e ∷ x }

reverse-Vec : (E : Set) → (n : ℕ) → Vec E n → Vec E n
reverse-Vec E n v = ind-Vec n v (λ { k _ → Vec E k }) [] (λ k e _ es → snoc-Vec E k es e)

