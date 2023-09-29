## Lecture 4 (2023-09-20)

In class a "judgement" is a judgement form; there are 4 or 5 of them


---

We have a "conv" law, which causestypingto depend on type equivalence

"conv" (e : B) × (A ≡ B) → e : A

---

Why does type equiv require deciding term equiv?
- due to "large elimination"
- we must allow computing a type by eliminating a term
- the example we have is (which-Nat e Nat (λ x Atom))

---

What is the eliminator for U?
- in a type annotation


> QUESTION
> hard time wrapping my head around Is Type and : U
> the rules sorta make sense on the board but I couldn't synthesize them because
  they seem unprincipled
