Quiz: Copy this file to MyWork, complete the proofs,
and submit it on Canvas. You have 10 minutes to finish
this quiz.

This problem tests your understanding of how
to reason about negations. Show that if *P* is
false the so is *P ∧ Q.
```lean
example (P Q : Prop) : ¬P → ¬(P ∧ Q) :=
_
```

This problem tests your understanding of classical
reasoning using the axiom of the excluded middle.
You are to prove this proposition by case analyis
using the axiom of the excluded middle. There are
of course four cases: P and Q both true, only one
or the other true, and both false.
```lean
open Classical
example (P Q : Prop) : P ∧ Q → Q ∧ P :=
let ponp := em P
let qonq := em Q
_
```
