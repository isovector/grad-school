# Lecture 3 - 2023-09-18

* A "value" is anything with a constructor at the top (WHNF)

How do we go about typechecking any of this?

Want:

> zero : car (cons ℕ ℕ)


Require:

> e : B × A ≡ B Type → e : A

with some janky rules for _≡_Type

---

We have some good refl judgments:

beta:
> e₁ ≡ e₁' : A , e₂ : B → (car (cons e₁ e₂)) ≡ e₁' : A


eta:
> → e ≡ (cons (car e) (cdr e)) : Pair A B

---



