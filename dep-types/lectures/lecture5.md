# Lecture 5 - 2023-10-04


```agda
data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> A

foldr : {A B : Set} -> List A -> B -> (A -> B -> B) -> B
foldr [] b _ = b
foldr (a :: as) b f = f a (foldr as b f)

length : {A : Set} -> List A -> ℕ
length x = foldr x (const suc) zero
```
