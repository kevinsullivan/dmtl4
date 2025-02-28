/- @@@
# HW 10. More Predicate Logic

We're posting the first set of HW10 problems
here, and will update this document later with
additional exercises in a bit. The problems here
are due before class Tuesday.

## PART I
@@@ -/


/- @@@
### #1

You've now seen that the proposition, ¬¬P → P,
is not constructively valid. But what about this
one: Is P → ¬¬P constructively valid? Prove it; or
if you get stuck, explain where any why. If you do
prove it formally, then give a corresponding English
language proof.
@@@ -/

example (P : Prop) : P → ¬¬P :=
_



/- @@@
### #2

Formally state and then prove that, for any
proposition, *P*, *P → ¬P → 0 = 1*.
@@@ -/

-- you answer here



/- @@@
### #3

Suppose P is any proposition. Prove ¬(P ∧ ¬P).
This theorem goes by the name, *no contradiction.*
@@@ -/

def noContradiction : Prop := ∀ (P : Prop), ¬(P ∧ ¬P)

example : noContradiction :=
_


/- @@@
### #4

There's an inference rule in propositional logic called
resolution. It's widely used in automated theorem provers
and satisfiability solvers. Suppose A, B, and P are any
propositions. Then (A ∨ P) → (¬P ∨ B) → A ∨ B is valid.
Hint: case analysis on P ∨ ¬P.

A. Bind the name, *resolution*, to this proposition.

B. Using *example* syntax, formally prove it's valid

C. Give an English language "proof" precisely explaining
the reasoning encoded in your formal proof, expressed in
fluent mathematical prose.
@@@ -/


-- Your answers here.
