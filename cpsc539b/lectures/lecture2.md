# Lecture 2 - 2023-09-13

## What is a PL?

1. Abstract syntax
2. Static semantics (judgments)?
    - Is this bound?
    - Is this well-typed?
3. Dynamic semantics
    - Evaluation


## Definition of Pie

### Syntax

e = Atom | ' (letters)+
  | Nat | zero | suc e
  | Pair A B | cons e e' | car e | cdr e


### Statics


→ e is Type
→ e : e'
→ Atom is Type
→ Nat is Type
→ z : Nat

e : Nat → suc e : Nat

e : A × e' : B → cons e e' : Pair A B


### Dynamics

car (cons e₁ e₂) → e₁
