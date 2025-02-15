/- @@@
# Propositions as Types by Example
@@@ -/


/- @@@
We will introduce the idea of representing
propositions as types with some simple examples
using *data* types in Lean.
@@@ -/


/- @@@

### A Few Elementary Propositions

Example: First we'll represent the proposition,
Kevin is from Charlottesville, as a data type,
and we will specify that it is true by defining
two proofs of it, represented as terms of this
type. We see the representation of "propositions
as types" for the first time, and that it's not
a terribly difficult idea to grasp! We'll use
*KC* as the name of a proposition that we will
take as expressing the claim that Kevin is from
Charlottesville.
@@@ -/
inductive KC where  -- A type
| DL                -- One proof
| EB                -- Another proof

-- Similarly for "John is from Charlottesville"
inductive JC
| DL
| EB

/- @@@
And finally we have the proposition that Mary is
from Charlottesville, but with no proofs, which
is how we'd represent the fact that Mary is *not*
from Charlottesville. If we can show that there
are no proofs of MC, then that shows that ¬MC must
be true!
@@@ -/
inductive MC where

/- @@@

## Conjunctive (∧) Propositions as Types
Now we'll see that we can represent the conjuctive
proposition, KC ∧ JC, as a new type having just one
constructor taking two proof values as its arguments:
a proof (value) of (type) KC and a proof of JC. If I
can apply KCandJC.intro to two such proofs then that
in effect proves that the conjunction is true, as the
arguments assure that each conjunct is true on its own.
@@@ -/
inductive KCandJC where
| intro (kc : KC) (jc : JC)  -- order changed from class

/- @@@
Here then a "proof" of the proposition. The key idea
here is that a value of this type holds a pair of proofs.
A proof of a conjunction is thus represented simply as a
data structure holding a pair of proofs.
@@@ -/

def pf1 : KCandJC := KCandJC.intro KC.EB JC.DL


/- @@@
We'll want to be able to express all kinds of
conjunctive (∧) propositions *without having to
define a new type, with a new name, for each of
them*. Each will have the same single constructor
taking the same kinds of proof arguments, but now
for many different sub-expression types. The trick
is to define *and* as a parametrically polymorphic,
a.k.a., generic, type. That's what we do here.
@@@ -/

inductive and (P : Type) (Q : Type) where
| intro (p : P) (q : Q)

/- @@@
 The result is a single type, *and*, representing
the ∧ connective in predicate logic. It takes any
two types, *P* and *Q* (we assume representing
propositions), as its arguments, reduces to a new
type, and this type represents the conjunction
of P and Q: written P ∧ Q in the concrete syntax
of predicate logic. With that we can now express
the proposition, KC ∧ JC, and "prove it" as follows.
@@@ -/
def pf2 : and KC JC := and.intro KC.EB JC.EB

/- @@@
Our *and* type is a type that in effect gives us a
way to define the type of any kind of pair, with a
first element of one type, P, and a second element
of a second type, Q.

In Lean 4, there is a built-in (Library-defined) type
called *Prod* (short for "product type") that serves
this very purpose. We could have used it instead, as
we see here.
@@@ -/

#check Prod
/- @@@
- Constructs a pair from two terms.
- The × operator is concrete notation for Prod
- Values of type P × Q hold pairs of values, first of type P then Q
- The first projection out of a pair. if `p : α × β` then `p.1 : α`.
- The second projection out of a pair. if `p : α × β` then `p.2 : β`.

  structure Prod (α : Type u) (β : Type v) where
  mk :: (fst : α) (snd : β)
@@@ -/

-- We can represent conjunction types using Prod
def andKCJC : Type := Prod KC JC
def andKCJC' : Type := KC × JC

-- Prove them as usual, now with Prod.mk instead of and.intro
def pf3 : andKCJC  := Prod.mk KC.EB JC.EB
def pf4 : andKCJC' := ⟨KC.EB, JC.EB⟩    -- concrete notation for mk

/- @@@
## Disjunctive (∨) Propositions as Types

We can represent disjunctions, such as KC ∨ JC, using the same
ideas, but now there are two ways to prove such a proposition,
one with a proof of KC and one with a proof of JC, as a proof
of either disjunct will suffice to construct a proof of the
overall disjunction. We'll run through the same thought process
now without lots of commentary.
@@@ -/

inductive KCorJC : Type where
| intro_left (pf : KC)
| intro_right (pf : JC)

/-@@@
A proof of a disjunction in this style is either a value
of this type holding a proof of KC or its a value of this
type holding a proof of JC. That means, among other things,
that we now have two different terms each of which serves
equally well as a proof of this disjunction. The first is
a proof of KC ∨ JC constructed from a proof of KC, and the
second is a proof of the same thing constructed from a proof
of JC.
@@@ -/
def pf5 : KCorJC := KCorJC.intro_left KC.EB
def pf6 : KCorJC := KCorJC.intro_right JC.EB

/- @@@
We can use parametric polymorphism (parameterized, or generic,
types) to define a general-purpose "or" type, just as we did
with and.
@@@ -/
inductive or (P Q : Type) where
| inl (p : P)
| inr (q : Q)

def pf7 : or KC JC := or.inl KC.EB
def pf8 : or KC JC := or.inr JC.EB

/- @@@
Lean provides a general purpose either/or type, called Sum
that we could have used instead of defining our own or type.
@@@ -/

#check Sum

/- @@@
Notice the concrete notation, ⊕, for Sum.
- Left injection into the sum type `α ⊕ β`. If `a : α` then `.inl a : α ⊕ β`.
- Right injection into the sum type `α ⊕ β`. If `b : β` then `.inr b : α ⊕ β`.

  inductive Sum (α : Type u) (β : Type v) where
  | inl (val : α) : Sum α β
  | inr (val : β) : Sum α β
  @@@ -/

def KCorMC' := Sum KC MC
def KCorMC := KC ⊕ MC     -- concrete syntax

/- @@@
We can prove Kevin or Mary is from Cville with a proof Kevin is,
but there's no proof that Mary is from Cville, so the "right" option
for proving the disjunction is not available to us.
@@@ -/
def korm : KCorMC := Sum.inl KC.EB

/- @@@
## We Can Now Express Arbitrarily Complex Propositions

With that we can represent more interesting propositions
as types. Here's "Mary is from Charlottesville or Kevin is
and so is John." In logical notation we'd typically write
this as MC ∨ (KC ∧ JC). Here's the proposition encoded as
a corresponding data type defined using Lean 4's generic
product (one of these *and* one of those) and sum (one of
these *or* one of those) types.
@@@ -/

def MC_or_both_KC_and_JC := MC ⊕ (KC × JC)

/- @@@
And here's a proof of it *in the form of a program*
that builds a "proof" (just a data structure) of the
right type. We cannot prove the left disjunct, that
Mary is from CVille, so the only way to prove this
proposition is to provide a proof of the right side,
that both Kevin and John are from CVille.
@@@-/

def pf9 : MC_or_both_KC_and_JC :=
  Sum.inr             -- prove right
    ⟨ KC.EB, JC.DL ⟩  -- proof of right

/- @@@
Finally, for now, what about negation? We should not
be able to prove ¬KC, because we've already established
that Kevin is from Cville, as there are proofs of it. On
the other hand, there's demonstrably no proof that Mary
is from CVille, so we can conclude that she's not: ¬MC.
We will construct such a proof by *case analysis* on all
of the possible proofs of MC to establish that there are
none, and that's what we will mean when we say that some
proposition is *not* true: there is demonstrably no way
to prove it.

For this, we will define a function from proofs of MC
(of which there are none), to proofs of Lean's *Empty*
data type, which is just another type with no values.
We will assume we're given a proof, mc, of MC, and we
will then instruct Lean to confirm that there are no
cases to consider. Every value of type MC will thus be
mapped to some value of type Empty, and fortunately no
values of type MC exist, otherwise this would not be at
all possible, since there are no values of type Empty
to map to!
@@@
-/

def prf_not_Mary : MC → Empty := λ (mc : MC) => nomatch mc

/- @@@
We can once again give a generalized definition here by
making the proposition type a parameter of a general "not"
operation. We'll call it neg here to avoid name conflicts.
@@@ -/

def neg (P : Type) := P → Empty

/-@@@
And with that we can express the proposition that Mary is
not from Charlottesville, and prove it!
@@@ -/
def notMC : neg MC := λ (m : MC) => nomatch m

-- Here's some notation for our version of neg
notation:max "~" p:40 => neg p

/- @@@
And with that we've got enough to write all kinds
of propositions familiar from propositional logic.
Here we assert and prove that Mary is from CVille
and either Kevin or John is: ¬MC ∧ (KC ∨ JC).
@@@ -/

def finalExample := ~MC × (KC ⊕ JC)

def pf10 : finalExample :=
  ⟨
    notMC,            -- pf mary not from cville
    Sum.inl KC.EB     -- pf at least one of K or J is
  ⟩

/- @@@
## Introducing Prop: The Type of all Logical Types

In the next class, we'll address some problems with
the approach we've taken here. The most obvious is
that it's impossible to distinguish types that are
used to represent propositions from types that are
meant to define ordinary data types.

There's a strong hint that there's something not yet
quite right with our examples, above, and that's that
the notations are wrong for logic! The Prod type that
we're using to represent conjunctions defines a family
of *data* types, as does *Sum*, with notations *×* and
*⊕*.

A second problem is that nothing prevents us from
passing ordinary data types as arguments to *and*
and *or* and *neg*, rather than just types that are
meant to represent propositions.

Third, we'd like to treat all proofs of any given
proposition as equally good and *not* have outputs
of computations depend on particular choices from
among available proofs of a given proposition.

The solution to such problems in type theory is to
define a new type universe, not *Type*, which is the
type/home of computational/data types, but *Prop*,
which becomes the type of all *logical*, which is to
say proposition-representing types.

Next class we'll see how Lean represents logical
*And*, *Or*, and *Not*, as taking arguments not of
any computational data types (not of type, *Type*),
but of the type, *Prop*, which in Lean is used as
the type of all types representing propositions.

We will thus have, for example, a generic type,
*And* that takes two types argument, but now where
each of these types (representing smaller propositions)
is of type *Prop*, not *Type*. Otherwise Lean's *And*
will be identifcal to *Prod*, but will be able to take
only proposition-encoding types as its arguments.

Lean will also define correct logical notations for
its polymorphic, logical-operator-representing types.
We write *P ∧ Q* instead of *P × Q*, *P ∨ Q* instead
of *P ⊕ Q*, and *¬P* instead of (our notation), *~ P*.

Finally, Lean will treat all values (proofs) of any
type in *Prop* as literally being equal, so there will
be no way for any ordinary computation to do one thing
given one proof and another given a different proof.
Lean will thus enforce what's known as the principle
of *proof irrelevance*.
@@@ -/
