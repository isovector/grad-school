# Lecture 6 (2023-10-11)


introdution forms correspond to type checking
    ( given a term and a type, show it works)
elimination is type synthesis
    ( generate a type given a term)

--------  --------
1 <= Nat  2 <= Nat
------------------
(1 + 2) => Nat syn    Nat = Nat
--------------------------------
(1 + 2) <= Nat  check              (3 + 4) <= Nat
--------------------------------------------------
(1 + 2) + (3 + 4) => Nat  syn

we can add in extra synth rules if we want (corresponding to the constructors)

can read these =>s as function arrows; the => direction makes a type, the <=
receives one
