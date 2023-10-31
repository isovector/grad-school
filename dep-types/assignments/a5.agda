module a5 where

open import Data.Nat
  hiding (_*_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; module ≡-Reasoning)
  renaming (sym to symm)

pattern same x = refl {x = x}
pattern add1 n = suc n

cong : {A B : Set} {x y : A} → x ≡ y → (f : A → B) → f x ≡ f y
cong refl f = refl



ind-Nat : (target : ℕ) → (motive : ℕ → Set) → motive 0 → ((n : ℕ) → motive n → motive (suc n)) → motive target
ind-Nat zero motive x x₁ = x
ind-Nat (suc target) motive x x₁ = ind-Nat target (λ z → motive (suc z)) (x₁ zero x) (λ n → x₁ (suc n))

sub1 : ℕ → ℕ
sub1 zero = zero
sub1 (suc x) = x

sub1-add1-inverse : (n : ℕ) → sub1 (add1 n) ≡ n
sub1-add1-inverse n = same n

+-assoc : (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
+-assoc x y z =
  ind-Nat x (λ x → x + (y + z) ≡ (x + y) + z) (same (y + z)) (λ { n p → cong p add1 })

step-+ = suc

which-Nat : {X : Set} → ℕ → X → (ℕ → X) → X
which-Nat zero x f = x
which-Nat (add1 n) x f = f n

+-right-zero : (n : ℕ) → n + 0 ≡ n
+-right-zero n = ind-Nat n (λ n → n + 0 ≡ n) (same 0) λ { n₁ x → cong x step-+ }

+-right-add1 : (n m : ℕ) → add1 (n + m) ≡ n + add1 m
+-right-add1 n m =
  symm (ind-Nat n (λ n → n + add1 m ≡ add1 (n + m)) (same (add1 m)) (λ x x → cong x step-+  ))

add1-sub-almost-inverse : (n : ℕ) → add1 (sub1 n) ≡ which-Nat n 1 (λ n-1 → n)
add1-sub-almost-inverse n =
  (ind-Nat n (λ n → add1 (sub1 n) ≡ which-Nat n 1 (λ n-1 → n) ) (same 1) (λ n _ → same (add1 n)))


rec-Nat : ℕ → {X : Set} → X → (ℕ → X → X) → X
rec-Nat zero x₁ x₂ = x₁
rec-Nat (add1 n) b f = f n (rec-Nat n b f)

max : ℕ → ℕ → ℕ
max n = rec-Nat n (λ x → x) λ { n-1 max-of-n-1 k → which-Nat k (add1 n-1) (λ k-1 → add1 (max-of-n-1 k-1)) }

-- +-assoc zero y z = same (y + z)
-- +-assoc (add1 x) y z = cong (+-assoc x y z) add1


max-idempotent : (n : ℕ) → n ≡ max n n
max-idempotent n = ind-Nat n (λ n → n ≡ max n n) (same 0) λ n₁ x → cong x step-+

max-zero-right : (n : ℕ) → max n 0 ≡ n
max-zero-right n = ind-Nat n (λ n → max n 0 ≡ n) (same 0) (λ x _ → same (add1 x))

_*_ : ℕ → ℕ → ℕ
n * j = rec-Nat n 0 (λ n-1ig *-of-n-1 → j + *-of-n-1)

+-comm : (n m : ℕ) → n + m ≡ m + n
+-comm n m = ind-Nat n (λ n → n + m ≡ m + n ) (symm (+-right-zero m)) λ { n x → trans (cong x step-+) (+-right-add1 m n)  }

*-zero-l : (n : ℕ) → 0 * n ≡ 0
*-zero-l n = ind-Nat n (λ n → 0 * n ≡ 0) (same 0) (λ n₁ x → x)

*-one-l : (n : ℕ) → 1 * n ≡ n
*-one-l n = ind-Nat n (λ n → 1 * n ≡ n) (same 0) (λ n₁ x → cong x step-+)

*-left-add1 : ∀ a b → ((1 + a) * b) ≡ b + a * b
*-left-add1 a b = ind-Nat a (λ a → ((1 + a) * b) ≡ b + a * b) (same (b + 0)) λ { n x → cong x (b +_) }

reassoc : (a b c : ℕ) → a + (b + c) ≡ b + (a + c)
reassoc a b c = trans (+-assoc a b c) (trans (cong (+-comm a b) λ { φ → φ + c }) (symm (+-assoc b a c)))

*-right-add1 : ∀ a b → a * (1 + b) ≡ a + a * b
*-right-add1 a b =
  ind-Nat a (λ a → a * (1 + b) ≡ a + a * b) (same 0) λ { n x →
    trans (cong x (λ φ → add1 b + φ)) (cong (reassoc b n (n * b)) add1)
  }

*-left-add1' : ∀ a b → ((1 + a) * b) ≡ b + a * b
*-left-add1' zero b = refl
*-left-add1' (add1 a) b =
  begin
    (1 + add1 a) * b
  ≡⟨⟩
    b + (add1 a) * b
  ≡⟨⟩
    b + (b + a * b)
  ≡⟨⟩
    b + (b + a * b)
  ≡⟨⟩
    b + (add1 a * b)
  ∎
  where open ≡-Reasoning

*-zero-r : (n : ℕ) → n * 0 ≡ 0
*-zero-r n = ind-Nat n (λ n → n * 0 ≡ 0) (same 0) (λ n₁ x → x)



