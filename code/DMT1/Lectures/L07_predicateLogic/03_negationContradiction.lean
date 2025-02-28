/- @@@
# Proof by Negation and by Contradiction

<!-- toc -->
@@@-/

/- @@@
## Introduction
We will now look further into reasoning about negations.
There are two related but fundamentally distinct axioms,
(often called *proof strategies* in traditional courses)
at play. With *P* standing for any proposition, the first
proof strategy applies the axiom of negation introduction
*(P → False) → ¬P)*, while the second applies the axiom of
negation elimination: *¬¬P → P*.

## Proof by Negation

In propositional logic we semantically validated the
proposition that *(P → ⊥) → ¬P* and called it negation
introduction. That is what logicians would call the way
of reasoning. It's common (though not widely used) name
is *proof by negation.*

Let's translate the propositional logic version into English
to get a lock on what it's saying. Reading from let to right
it says that *if assuming P is true implies False (leads to
a contradiction), then it one can validly conclude ¬P.* The
so-called *strategy* of proof by negation is just the use
of this rule. If you're goal is to show *¬P* then this is the
way you do it: by showing that if you assume that *P* is true
you can then show that False is true, which it isn't so *P*
isn't, and *¬P* is a valid conclusion.

As an example, just consider our earlier proof that, say,
*1* is not even. To prove it we assumed that *1* is even,
as shown by an assumed proof, *h*, and then we showed by
*nomatch* that there are no such proofs, which is to say
that *1 is even* demonstrably cannot be proved, and so is
demonstrably false, We conclude *¬Ev 1*.

## Proof by Contradiction

Proof by contradiction, on the other hand, corresponds to
the *elimination* rule for negation. Refer back to the
propositional logic *axioms* file. This is the axiom that
says that two *nots* cancel out: *¬¬P → P*. An example of
this form of reasoning is, if it's not not raining, then
it is raining.

To understand proof by contradiction you just have to unpack
this proposition. In particular, unfold the outer *¬* sign.
*¬* de-sugars to *not P* and that is defined as *P → False*,
so unfolding the outer instance of *¬*, reducing *¬(¬P)* to
*(¬P → False)*. The negation elimination is thus equivalent
to *(¬P → False) → P*. In other words, this "axiom" asserts
that to prove a proposition *P* (not the negation of *P*),
it suffices to show that assuming that *P* is false (*¬P*)
leads to a contradiction.

As an example, consider the proposition, *the sum of any
even natural number, *n*, and any odd natural number, *m*,
is odd. Proof. We will assume that *n + m* is not odd (that
it is even); will then show that this assumption leads to
an impossibility, leading to the conclusion (by proof by
negation!) that it's not the case that *a + b* is not odd.
Finally, and here's the clincher, we'll using *negation
eliminiation* to infer from that that *a + b* is odd. If
we didn't have negation elimination it's exactly that last
reasoning step that is blocked.

So suppose *n + m* is not odd. Then it's even. As it's even
we can write *n + m* as *2 \* k* for some integer k. In the
same vein, as *m* is odd, we can write it as *2 * j + 1* for
some *j*. Their sum, *m + n* is thus *2\*k + *2\*j + 1*. This
in turn is *2 * (k + j) + 1*. That's odd, which is directly
at odds with our assumption that *m + n* is not odd. By the
rule of negation introduction (proof by negation) we conclude
that *m + n* is not odd is false. That is *m + n* is not not
odd (the double negation is not a typo). Then by the axiom
of negation elimination (double negation cancellation) we
finally conclude that *m + n* really must be odd after all.

## Negation Elimination is Not an Axiom in Lean

We use *negation introduction* extensively when working in
Lean: it's just how you prove *negations of propositions*.
Perhaps shockingly, though, negation elimination is not an
axiom in Lean. In other words, it is not, be default, a way
that you can reason in the constructive logic of Lean. The
is that from a given/assumed proof of *¬¬P* there's no way
to derive a proof of *P*. Having a proof that *¬P* is false,
i.e., of *((P → False) → False)* is not enough to get a proof
of *P*. Here's how you get stuck if you try to prove that it
is a valid reasoning principle.
@@@ -/

example (P : Prop) :  (¬¬P) → P :=
-- assume ¬¬P, defed as ((P → False) → False)
fun nnp =>
-- now try to show (return a proof of) P
_ -- stuck!
-- you can't prove P from ((P → False) → False)

/- @@@
It's usually counterintuitive at first that knowing *¬P*
to be false is not enough to conclude that *P* is true,
but that's exactly the case in constructive logic.
@@@ -/

/- @@@
## Classical Reasoning

On the other hand, if you want to reason *classically*, to
includ proof by contradiction, with negation elimination as
an axiom, then you just have to tell Lean that that is an
axiom. The axiom doesn't contradict Lean's logic, so it can
be added to or left out at will. It's non-constructive and
so is left out by default.

### Adding Negation Elimination as an Axiom to Lean

Here's it looks like to add it as an axiom to Lean. The
axiom has a name and a proposition that is henceforth taken
to be valid without proof. We hide the defunition inside a
namespace so as not to *pollute* our reasoning environment
with an axiom we might or might not want to use.
@@@ -/

namespace myClassical

axiom negElim : ∀ (P : Prop), ¬¬P → P

/- @@@
That's it. In English this says, "Assume as an axiom,
without further proof, that for any proposition, *P*,
if you have a proof of *¬¬P* you can derive a proof of
*P*.

As a trivial but still illustrative example, we can prove
the proposition, *True* is valid, not by a direct proof
*(True.intro)*, by rather by contradition: applying our
new axiom of negation elimination to a proof that we will
construct of ¬¬True.
@@@ -/

example : True :=
negElim -- eliminate double negation obtained by
  True    -- by proving the negation of True to be false (¬¬True)
  (fun (h : ¬True) => (nomatch h)) -- which is what happens here
-- Note that *P* in our definition is an *argument* to *negElim*


/- @@@
### The Equivalent Axiom of the Excluded Middle

Another way to enable classical reasoning in Lean is to
add a different non-constructive axiom, namely the law of
the excluded middle. What does it say? That there are only
two possibilities for any proposition: it's either valid or
it's not valid, and so if you know that one of these states
does *not* hold, then you know for sure that the other one
must. In other words, for any proposition, *P*, you can have
a proof of *P ∨ ¬P* *for free*, without presenting either a
proof of *P* or a proof of *¬P*. One can then reason from
this proof of a disjunction by case analysis, where you can
assume a there's a proof of *P* in the first case and there
is a proof of *¬P* in the second, and only other, case.
@@@ -/

axiom em : ∀ (P : Prop), P ∨ ¬P

/- @@@
From this axiom we can in fact derive negation elimination.
@@@ -/

example :
  (∀ (P : Prop), (P ∨ ¬P)) →
  (∀ (P : Prop), ¬¬P → P) :=
fun hEm =>
  (
    fun P =>
    (
      fun nnp =>
      (
        -- use em to get a proof of P ∨ ¬P
        let pornp := hEm P
        -- then use case analysis
        match pornp with
        | Or.inl p => p
        | Or.inr np => False.elim (nnp np)
      )
    )
  )


/- @@@
```lean
fun hEm =>
  fun P =>
    fun nnp =>
      match (em P) with
      | Or.inl _ => by assumption     -- a lean "tactic!"
      | Or.inr _ => by contradiction  -- a lean "tactic!"
```
@@@ -/

/- @@@
If fact it's an equivalence, in that you can prove that
negation elimination implies excluded middle, as well. You
can thus add either one as an axiom, derive the other and
then use either classical reasoning principle as you wish.
That proof is left as an exercise for the curious reader.

Moreover, each of these axioms is in fact derivable from
of even more fundamental axioms, such as the so-called
axiom of choice, which holds from any non-empty set of
objects you can always choose an element, even if there
is no constructive way to specify how that will be done,
and so from any infinite collection of sets you can always
construct a new set with one element from each of the given
sets. For more information, you might see the [Wikipedia
article](https://en.wikipedia.org/wiki/Axiom_of_choice)
on this topic.
@@@ -/

/- @@@
### Demorgan's Law Example: ¬(P ∧ Q) → (¬P ∨ ¬Q)

We've already gotten stuck trying to prove that for
any propositions, *P* and *Q*, ¬(P ∧ Q) → ¬P ∨ ¬Q.
We can however prove that this formula is valid in
classical logic by using the axiom of the excluded
middle. It is available in Lean 4 in the *Classical*
namespace as *Classical.em*. We'll thus now switch
to using Lean's standard statement of this axiom.
@@@ -/
end myClassical

#check Classical.em
-- Classical.em (p : Prop) : p ∨ ¬p

/- @@@
The axiom of the excluded middle takes any
proposition, *P*, for which we might have a
proof of *P*, or of *¬P*, or *neither,* and it
eliminates that third, *middle*, possibility.
It forces any proposition to have a *Boolean*
truth value. That in turn returns us to our
earliest form of reasoning about the validity
of a proposition over a some finite number of
combinations of the *Boolean* truth values of
its constituent elementary propositions. Here
we will show that DeMorgan's Law for negation
over conjunction is true under each of the four
possible combinations of Boolean truth values
for *P* and *Q*.
@@@ -/
example (P Q : Prop) : ¬(P ∧ Q) → ¬P ∨ ¬ Q :=
fun (h : ¬(P ∧ Q)) =>
/- @@@
At this point we're constructively stuck, as
*h* is just a proof of a function to False and
there's no way to derive a proof of either ¬P
or ¬Q from that.

But we have the juice proposition, *P*, to
work with, and from that, by excluded middle,
we can have free proof of *P ∨ ¬P*, at which
point we only have two cases to consider. Wd
do that by case analysis as when reasoning
from the truth of any disjunction.
@@@ -/
let pornp : P ∨ ¬P := Classical.em P
-- TRICK! Do case analysis on *pornp*
match pornp with
-- Case P is true (and we have a proof of it)
| Or.inl p => -- we now do case analysis on Q ∨ ¬Q
  match (Classical.em Q) with
  -- case P is valid and so is Q
  | Or.inl q =>
    let f : False := h (And.intro p q)
    False.elim f
  -- impossible case: finish it!
  -- case ¬P is true, so ¬P ∨ ¬Q is
  | Or.inr nq => Or.inr nq
-- Case P is false, in which case ¬P ∨ ¬Q is, too
| Or.inr np => Or.inl np
