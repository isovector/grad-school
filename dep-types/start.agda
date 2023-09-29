U = Set

data Nat : U where
  z : Nat
  add1 : Nat -> Nat

which-Nat : {X : U} -> Nat -> X -> (Nat -> X) -> X
which-Nat z b f = b
which-Nat (add1 n) b f = f n

four = add1 (add1 (add1 (add1 z)))
five = add1 four
six = add1 five

_+_ : Nat -> Nat -> Nat

-- open import Relation.Binary.PropositionalEquality
--
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
infix 0 _≡_


test1 : which-Nat five z (\x -> (six + x)) ≡ six + four
test1 = refl

iter-Nat : {X : U} -> Nat -> X -> (X -> X) -> X
-- Commandment 1: (iter-Nat zero base step) is the same X as base
iter-Nat z b f = b
-- Commandment 2: (iter-Nat (add1 n) base step) is the same X as
--   (step (iter-Nat n base step))
iter-Nat (add1 n) b f = f (iter-Nat n b f)

e1 + e2 = iter-Nat e1 e2 (λ z₁ → (add1 z₁))
-- 0 + e2 = e2
-- (add1 n) + e2 = (?? (iter-Nat n e2 ??))

ten = add1 (add1 (add1 (add1 (add1 five))))

test2 : (five + five) ≡ ten
test2 = refl

-- Exercise 1: Define the type of rec-Nat
rec-Nat : {X : Set} → Nat → X → (Nat → X → X) → X
rec-Nat z b _ = b
rec-Nat (add1 n) b f = f n (rec-Nat n b f)

-- Exercise 4: Finish the definition of gauss
step-gauss : Nat → Nat → Nat
step-gauss n gauss = (add1 n) + gauss

gauss : Nat → Nat
gauss n = rec-Nat n z step-gauss

-- Exercise 4: Prove (gauss five) is equal to 15
test3 : (gauss five) ≡ (five + ten)
test3 = refl

