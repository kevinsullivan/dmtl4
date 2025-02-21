# Connectives

<!-- toc -->

-----------
## And (∧)

### Introduction

Here we apply And.intro to construct proofs of P ∧ Q.
In each case it's by applying the proof/value constructor,
And.intro to arguments, p and q, of types P and Q, respectively.
The first example binds a name to the resulting proof so we can
use it later. The second example checks the proof but doesn't
give it a name. The third example presents concrete notation,
defined in Lean's libraries, for And.intro _ _
```lean
def pandq : P ∧ Q := And.intro p q
example   : P ∧ Q := And.intro p q
example   : P ∧ Q := ⟨ p, q ⟩
```

### Elimination

From a proof, pandq, of P ∧ Q, we can derive proofs of P and
of Q, respectively. We do this by destructuring a given proof,
such as pandq. There's only one constructor, but destructuring
let's us get at the two smaller proofs from which any such term
must have been constructed. It's especially easy to apply the
elimination rules because (1) there's one constructor, And.intro,
(2) the type is defined using the "structure" keywords, and (3)
as a result of that, we can use the names of the fields, given
in the definition of And, to retrieve that arguments that were
given to And.intro when the value was constructed.
```lean
example : P := pandq.left
example : Q := pandq.right
example : P := pandq.1
example : Q := pandq.2
```

A little theorem

```lean
example : P ∧ Q → Q ∧ P
| And.intro p q => And.intro q p
```



## Or (∨)

### Introduction

A proof of P ∨ Q can be constructed from a proof (p : P) or
from a proof (q : Q), for which we have the two constructors,
Or.inl and Or.inr.

```lean
def porqFromP : P ∨ Q := Or.inl p
def porqFromQ : P ∨ Q := Or.inr q
```

### Elimination

```lean
#check (@Or.elim)
```

The check shows the type of Or.elim.  It's a function of this type:
∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c. It says that if a,
b, and c are any propositions, then if you have a proof, (h : a ∨ b),
then if we also have proofs, (ac : a → c), and (bc : b → c), then in
either case of h (one carryiny a proof of a, and the other a proof of
b) we can construct a proof of c, by applying either ac or bc to the
proof of a in the first case and b in the second case. This will show
that if you have *any* proof of a ∨ b along with proofs of ac and bc,
then you can derive a proof of c.

To see this rule in actions, let's just assume, without being specific,
that we do have have proofs of ac : a → c and bc : b → c. They will be
in the form of functions, as we've seen several times now. Because we've
already defined R to be an empty type, we'll introduce one more type, S,
to illustrate these ideas.

```lean
axiom S : Prop
axiom ps : P → S
axiom qs : Q → S


#check (Or.elim porqFromP ps qs)
-- This term, (Or.elim porqFromP ps qs), serves as a proof of S!
```

A little theorem.

```lean
example : P ∨ Q → Q ∨ P
| Or.inl p => Or.inr p
| Or.inr q => Or.inl q
```

Proof:
Assume P ∨ Q is true with a proof, call it h. There are
two cases to consider.
Case 1: P ∨ Q is true because there's a proof, (p : P).
In this case, Or.inr (on the right) is a proof of Q ∨ P.
Case 2: P ∨ Q is true because there's a proof, (q : Q).
In this case, Or.inl (on the left) q is a proof of Q ∨ P.
Those are all the cases for a proof of P ∨ Q, so *whenever*
we're given a proof of P ∨ Q we can derive a proof of Q ∨ P,
so P ∨ Q → Q ∨ P is valid.



## Implication

### Introduction

As we've explained, to prove the proposition, P → Q, in
type theory, one must show that there is (one must define)
a total function from P to Q. A total function is one that
works for all values of the argument type.

To make a few more interesting examples, let's recall our
our natural number evenness predicate.

```lean
inductive Ev : Nat → Prop
-- Note: Ev 0 in the following is a proposition
-- ev0 serves as a proof of Ev 0 (which we read as "zero is even")
| ev0 : Ev 0
-- Given n and proof that n is even we can have a proof that n+2 is even
| evFromEv : (n : Nat) → (evn : Ev n) → (Ev (n + 2))
```


The first constructor makes (Ev 0) an axiom by defining ev0
is a proof of it. The second constructor, evFromEv, makes our
second rule defining evenness into an axiom: in this case it is
accepted as a proof of (n : Nat) → (evn : Ev n) → (Ev (n + 2).
As it's a proof of an implication in type theory, it can also
be treated as a function, and as such, when *applied* to an n
and a proof that that n is even, the result is a proof that n+2
is even. We have thus given an *inductive definition* of the
one-place predicate, Ev, representing the mathematical concept
of evenness. It also gives us a nice way to define what we mean
by the infinite set of even numbers: it's the set of just those
numbers, n, for which there are proofs of evenness as we've
just defined it.

A cool observation is that you can't even *apply* evFromEv
to its arguments if n isn't even, because you can never have
a proof that that n is even.

Here are Lean-checked (correct) proofs that 0, 2, 4, and 6 are even.
```lean
open Ev

def zeroEv  : Ev 0 := (Ev.ev0)
def twoEv   : Ev 2 := (evFromEv 0 zeroEv)
def fourEv  : Ev 4 := (evFromEv 2 twoEv)
def sixEv   : Ev 6 := (evFromEv 4 fourEv)
```

Here's a proof of a theorem: if any natural number, n,
is even, then so is n+4. The proof is by two applications
of the inductive step. First from the assumed n and proof
of Ev n, a proof of Ev (n+2) is constructed. Then from n+2
and that latter proof, a proof of n+4 is constructed. QED.


```lean
open Ev
def IfEvNThenEvNPlus4 : (n : Nat) → (Ev n) → Ev (n + 4)
| n, evn => evFromEv (n+2) (evFromEv n evn)
```

Finally, to get back to the main topic of this section,
you prove an implication, such as P → Q, by showing, in
the form of a function of type P → Q, that there is a way
to derive a proof of Q from any proof of P. For example,
the proof we just gave is a function. For any Nat, n, then
from a proof of (Ev n) it *computes* a term that typechecks
as a proof of Ev (n + 2). As long our Ev axioms really do
capture what we mean by evenness then such a proof object
will check as a correct proof that that n is even.

### Elimination

So how do you use a proof of P → Q, which in Lean is again
in the form of a function, from P → Q? You just *apply* it:
to a specific proof of P to get a proof of Q. As an example,
we proved that if n is even so is (n+4). We actually have a
proof object, called IfEvNThenEvNPlus4. It's a function. If
we apply it to, say, n = 6 and a proof that 6 us even, it
will compute and return a proof that 10 is even!Check it out!

```lean
#check  IfEvNThenEvNPlus4 6 sixEv
--      IfEvNThenEvNPlus4 6 sixEv : Ev (6 + 4) <-- proof Ev 10
```



## Negation (¬)

Recall that at the top of this file we defined F to be a
proposition (type) with no proofs at all. No constructors
means no proofs, as the only proofs of a type are those that
can be constructed using one of the provided constructors.

### Introduction

Given that F is a proposition with no proofs, we interpret
it as false, and should thus be able to prove that ¬F is true:
that there's a proof of it. Recall that ¬F is defined to be
the proposition F → False, where False is the standard empty
propositional type in Lean. Again the trick to prove ¬F is to
to remember that it simple means F → False.

A proof of that is a proof of an an implication, and in type
theory, that means a function that turns any assumed proof of
F into a proof of False. As we've already reasoned about, it
is possible to define such a function if and only if F is an
uninhabited type. The only trick is that you remember that
to prove ¬F is defined to be identicall to proving F → False.

```lean
def notF : ¬F       -- this is defined to mean F → False
| f => nomatch f    -- assuming a value of type F is absurd
```

### Introduction: Proof By Negation

So that the introduction rule for negation. To construct a proof
of ¬F it suffices to construct a proof of F → False. Now how should
express this in English? To prove ¬F, assume that F is true, and in
this context you can prove a contradiction (e.g., that False is true).
If you can (and if the logic itself is consistent) the conclusion one
must draw is that F cannot be true in the first place.

Now something quite important: In a traditional paper-and-pencil
discrete math class using first-order logic and set theory, you might
be taught that this form of reasoning is called "proof by contradiction:"
assume F, show False, conclude ¬F. But that is not accurate enough.

Ratherm this form of reasoning, (F → False) ⊢ ¬F, is called *proof by
negation.* To prove a negation, ¬F, it suffices to prove F → False. In
type theory, such a proof is a function, the existence of which proves
that there can be no proofs of F, which is what we mean by F is false,
which is what we mean by ¬F is true.

Summary: We saw in propositional logic that P ⇒ ⊥ ⇒ ¬P. Here in type
theory, we have (F → False) ⊢ ¬F as an axiom: If we have a proof of
F → False, we can conclude (in fact that same proof is a proof of) ¬F.

### Elimination: Proof by Contradiction

Proof by contradiction is the *elimination* rule for negation. It is
perhaps better remembered as the rule of *double* negation elimination.
In propositional logic, the analog is neg_elim, stating that ¬¬P ⇒ P.
It asserts that you can always eliminate double negations: two nots
cancel out. This statement is clearly valid in PL as it's true in the
underlying Boolean algebra.

This rule embodies the so-called proof strategy of proof by contraction.
In English, we say this: The goal is to prove P. To do this assume ¬P and
show that this assumption leads to a contradiction (e.g., proof of False).
Assuming ¬P and showing False proves ¬¬P. And as long as ¬¬P → P is valid,
that suffices to prove P.

Another way to say this is that if you want to prove P, assume ¬P, show
a contradiction, then conclude ¬P is false, thus ¬¬P must be true, then
by double negation elimination, P must be true. In summary, the axiom of
negation introduction, P → False ⊢ ¬P, defines *proof by negation*, while
the axiom of negation elimination ¬¬P ⊢ P defines proof by *contradiction.*

We've already seen that proof by negation is straightforward in Lean. What
will surely shock you greatly now is to learn that proof by contradiction,
i.e., double negation elimination, *is not an axiom in type theory*. The
axioms of Lean do not include ¬¬P → P as an axiom.

To understand why, you now need to complete the shift in your thinking
from truth-functional (Boolean function) to proof-functional reasoning.
To see that ¬¬P → P is not true in Lean, just suppose you have a proof
of ¬¬P. What you would need to do is to show that from it you can get a
proof of P. But you can't.

To see why, expand the definition of each ¬ connective. Recall ¬P is
defined as P → False. So ¬¬P means ¬(P → False) and this in turn means
(P → False) → False. Just look at this type: it's a function that if
applied to a proof of ¬P would yield of proof of False. The details
don't matter as much as the insight that this proof is a function and
there's no proof of P sitting insider of a function that returns False.

But that's all complicated. Let's think in English. In *classical*
logical reasoning, there are only two possible judgements about any
proposition, P: it's either true or it's false. There is no muddled
middle truth value. In the *constructive* logic of type theory (and
Lean), knowing that ¬P leads to a contradiction doesn't give you a
proof of P, which is what you need to conclude that P is true.

To see in more detail what the issue is, let's just try to prove a
that a statement of neg_elim in Lean is valid and we'll see where we
get stuck. With α being any proposition, we'll try to prove ¬¬α → α.

```lean
example (α : Prop) : ¬¬A → A
| pf => _   -- stuck: need proof of A; only have weird function
```


## Classical Reasoning

In "classical" logic, such as propositional logic, the
rules of negation elimination, thus proof by contradition,
are valid. In the constructive logic of Lean they're not.
By the term, constructive, we mean that we actually have
to be able to *construct* a proof of a proposition before
we can consider it to be true. The problem with negation
elimination is that we simply can't construct a proof of
a proposition α if all we know is there's no proof of ¬α
(that ¬¬α must be true).

And yet an enourmous amout of mathematics uses proof by
contradiction. Can we not do ordinary mathematics in Lean?
The answer to that is no, that's not what it means. To do
classical reasoning in Lean, you just have to tell Lean
to accept negation elimination as an axiom!

```lean
axiom neg_elim : ∀ {α : Prop}, ¬¬α → α
```


In English that says, Hey Lean. Trust me. You can just
accept that for any proposition, α, if one has a proof of
¬¬α one can simple assume that one can get a proof of α,
and that would be by applying neg_elim!

For example suppose I want to prove P by contradiction
and that I've managed to get a hold of a proof (nnp : ¬¬P).
A proof of P is had by apply negation elimination to nnp.

```lean
axiom nnp : ¬¬P               -- assume I have a proof of ¬¬P
def pfP : P := (neg_elim nnp) -- neg_elim applied to nnp proves P
```

### Excluded Middle

The main "problem" with negation elimination is that it just
"pretends" that it yields proofs of P from proofs of ¬¬P. A
real proof of P in Lean could be a very complex object, but if
one gets a "pretend" proof of P by applying this axiom, it will
contain none of that detail. No real proof of P is constructed.
We say the axiom of negation elimination is *non-constructive*.

One of the important consequences of the axiom of negation
elimination is that it drives every proposition, P, to be either
true, with a proof (p : P) or false, with a proof (np : ¬P),
with no muddled middle state where one doesn't have a proof
either way. In the preceding example, we could not conclude
that P is true from a proof that ¬P is false, but with the
axiom of negation elimination we can. We can formalize this
statement as another axiom: the so-called law of the excluded
middle.

```lean
axiom excludedMiddle (α : Prop) : P ∨ ¬P
```

Indeed, it turns out that if neg_elim is accepted as an
axiom, then excludedMiddle can be proved, and vice versa!
They are equivalent. It's a litte challenge to prove that!

```lean
def equiv (P : Prop) : ¬¬P ↔ (P ∨ ¬P) := _
```

The proof is left as an exercise!
