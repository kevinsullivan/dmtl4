# Propositional Logic with Proof-Theoretic Validity

In this chapter, we re-develop propositional logic in type theory,
but now with a *proof-theoretic* rather thana model-theoretic notion
of what it means for a proposition to be *valid*. Rather than checking
all interpretations, we will embed the axioms of propositional logic
into Lean and then we weil *reason* about validity using them:

- We will represent any given proposition as a *type*
- We will represent the proofs of a proposition as the *values* of its type
- The values of a type are given by its constructors; picking the right constructors is the trick
- We (and Lean) will accept any value/proof of a proposition/type as a proof of its validity/truth
- If a proposition/type demonstrably has *no* values (no proofs), we'll consider it to be false
- We will represent elimination axioms as functions that take proof arguments and return proof results

To make all of this concrete, we'll do the following in the rest of this lecture:

- represent two propositions as corresponding types
- use cleverly designed constructors to express introduction rules
- use functions that consume and return proof values to express elimination rules
- use all of this machinery to prove an interesting identity (*And* is commutative)

## Propositions as Types; Values as Proofs

We now represent two propositions as type: Kevin is from Charlottesville,
and Carter is from Charlottesville. We'll use K and C as shorted names for
these propositions. We'll go on to define three *values* of each type, each
one to be considered as a proof.

```lean
-- Kevin is from Charlottesville
inductive K : Type where                            -- proposition as a type
| cvilleBirthCert                                   -- a proof as a value
| cvilleDriversLicense                              -- another proof
| cvilleUtilityBill                                 -- a third proof

-- Proposition: Carter is from Charlottesville
inductive C : Type where
| cvilleBirthCert
| cvilleDriversLicense
| cvilleUtilityBill

-- Kervin is from LA
inductive KLA : Type where

-- later we'll replace these two propositions with one predicate
-- we can also see here that a proposition can have multiple proofs

open K
open C

-- We can now "give proofs" of our two respective propositions

--  proof name  proposition/type    proof/value
def pfK      : K :=              K.cvilleDriversLicense
def pfC      : C :=              C.cvilleUtilityBill
def pfKLA    : KLA :=            sorry
```

We've introduced no new Lean constructs at this point. We've just
proposed a way to use what we already know about types and values.
By same reasoning we could even think of 1 as a proof (one of many)
of Nat. We won't find it particularly useful to think this way, but
the point is to see that so far we've seen nothing new in Lean, just
a weird new way to represent propositions (as types) and proofs (as
values of such types). That's it!

```lean
--  proof name    proposition/type  proof/value
def proofOfNat    : Nat             := 1
```


## The Axioms Behind The Logical Connectives

Ok, so we've represented two propositions as types, each with
three values. We will consider each such value as a "proof" of
the validity/truth of the proposition.

That's all good, but what about the logical connectives? We
have two propositions each with proofs already in hand. Four
major questions leap to mind. (1) How can we use types to
represent complex propositions, such as (K ∧ C), (K ∨ C) ,
or ¬K? (2) What constructors will we provide to embody and
enforce the distinct meanings of each of the  connectives.
(3) How will we be able to use such proofs to derive new proofs?
(4) Can we prove interesting theorems (important propositions)
using these tools?

The trick is going to be to perfectly represent the *axioms*
that define each logical connective using types and functions.
As a first, and the easiest, example consider once again the
*And* (∧) connective. It's intended meaning is captured by
the corresponding axioms.

### Conjunctions: *And* Propositions

Suppose P and Q are propositions and recall the axioms for
*And.* There's one "rule" (axiom) for *constructing* a proof
of P ∧ Q, and there are two rules for *using* a proof of P ∧ Q:
to derive a proof of P, or a proof of Q.

As a reminder, here are the axioms as we've already studied
and stated them. They first says that from separate proofs of
P and Q you can derive a proof of P ∧ Q. The second and third
say that from a proof of P ∧ Q, you can derive proofs of P and
of Q, respectively.

- and_intro:      P → Q → P ∧ Q
- and_elim_left:  P ∧ Q → P
- and_elim_right: P ∧ Q → Q

The propositions-as-types trick is to represent introduction
rules as constructors, and elimination rules as functions that
take proofs as arguments and that do case analysis on them.

We'll thus represent and_intro as a constructor, and and_elim_left
and and_elim_right as functions. These functions in turn will use
pattern matching (which you also already understand) to determine
what constructors and what arguments were used to construct given
proofs, so that these values can be used in building new proofs.


#### Introduction Rule

We will represent the proposition, K ∧ C, that Kevin is from
Cville *And* Carter is from Cville, as a new type, here called
KandC. We want a proof of and to be constructable from a proof
of K and a proof of C. So we will define a *constructor* that
works just this way. We'll call it *intro* and it will *requre*
proofs of K and of C as separate arguments to complete its task.
We will provide no other constructors, so the *only* way to prove
KandC will be to give separate proofs of K and C to the *intro*
constructor.

```lean
-- First, here's a type and proof constructor for this proposition
inductive KandC : Type where
| intro (kp : K) (cp : C)


-- The type of the constructor reveals how it encodes and_intro (compare!)
#check (@KandC.intro)
```


Now let's use "intro" rule to construct a proof (value) of KandC

```lean
--  proof name (value)  proposition/type  proof/value of ∧ proposition from proofs of conjuncts
def pfKandC :           KandC :=  (KandC.intro pfK pfC)
```

#### Elimination Rules

Yay! So now what about the two elimination rules?

- and_elim_left   : P ∧ Q → P
- and_elim_right  : P ∧ Q → Q

We will implement these elimination rules as functions. Each one
will take a proof of the conjunction (such as *pfBoth*)
and will return one of the two component proofs: either K or C. It
should be clear that these functions precisely represent the "elim"
rules that define the behavior of the logical *And* connective!

```lean
def KandC_elim_left : KandC → K
| KandC.intro k c => k            -- note: can replace c with _

def KandC_elim_right : KandC → C
| KandC.intro _ c => c            -- actually replaced k with _

-- KandC → K
#check (@KandC_elim_left)

-- KandC → C
#check (@KandC_elim_right)
```

The "elimination" axioms for *And* are represented by these
functions. But we now have more than just paper-and-pencil logic;
we have functions that compute! Let's see them in action: first
P ∧ Q → P, then P ∧ Q → Q.

```lean
#reduce KandC_elim_left pfKandC   -- proof of K (driver's license)
#reduce KandC_elim_right pfKandC  -- proof of C (utility bill)
```

#### A Theorem

We previously determined that the proposition that
*And is commutative* is value, using our semantic, or
model-theoretic, notion of validity. Now we will prove
it deductively (from the axioms) using proof-theoretic
reasoning.

We already have a type, and have constructed a proof
of what amounts to K ∧ C (of KandC). From this proof
can we derive a proof of C ∧ K? We'll need a new type
to represent this new proposition. It'll look just
like the KandC type, along with its elim functions,
but with the K and C reversed. What we then want to
prove is, in essence, K ∧ C → C ∧ K: that if we have
a proof of K ∧ C (which we do, namely *KandC*), we
can derive from it a proof of C ∧ K?

```lean
-- intro: C → K → C ∧ K
inductive CandK : Type where
| intro (c : C) (k : K)

-- elim_left: C ∧ K → C
def CandK_elim_left : CandK → C
| CandK.intro c _ => c

-- elim_right: C ∧ K → K
def CandK_elim_right : CandK → K
| CandK.intro _ k => k
```

### Implication

To finish off this introduction to logical reasoning using
type theory, we prove that K ∧ C → C ∧ K (here in the form
of the proposition KandC → CandK). We will give a proof of
this implication in the form of a *function*. This function
will take/assume a proof/value of type KandC as an argument.
It will use the KandC elim rules to obtain separate proofs of
K and of C. And it will finally pass them as arguments, in
the reverse order, to CandK.intro constructor. This shows
that from any proof of KandC we can derive a proof of CandK!

```lean
def andCommutes : KandC → CandK
| KandC.intro k c => CandK.intro c k
```

To the left of the =>, we analyze the given/assumed proof
of KandC, extracting its component proofs, then on the right
side of the => we use those component proofs, in a different
way, to construct a proof of CandK.

The existence of this function, one that can take any proof
of KandC and turn it into a proof of CandK, shows that if
KandC is valid/true, as demonstrated by having a proof of
it, then so is KandC, as a proof of it can be constructed
from the proof that is given/assumed. This is exactly what
it means to say that KandC *implies* CandK. But now instead of
just thinking truth-functionally (if KandC is *true* then so
is *CandK*) we now think proof-functionally (if you have or
assume a *proof* of KandC then you can *derive* a *proof* of
CandK).

It's no mistake that we're using the same → notation for
both logical implication and a function type. What does a
function definition say? *If* you give me arguments of the
required types, then I'll produce a result of the required
return type.

A proof of an implication, P → Q, in type theory, is thus
a function: taking any proof of P as and argument and then
deriving/constructing a proof of Q as a return value.

We thus have our *introduction* rule for implication. To
prove P → Q, exhibit is a function implementation that takes
any proof, (p : P), and that returns a result, (q : Q).

So what is the elimination rule for implication? See the
rule in the axioms file. It reads as this: (P → Q) → P → Q.
If you have a function, (f : P → Q), that turns P proof/values
into Q proofs/values, and then if you also have a value,
(p : P), then then you can derive a proof/value of type Q.
How? By *applying* the P-to-Q function to that value (p : P).

As a demonstration to finish this lecture, we do that now.
We have a proof of KandC → CandK, in the form of the function,
andCommutes, and we have a proof of K, namely *pfK*. We can thus
expect that applying *andCommutes* to *pfK* will return a proof
of CandK. And indeed it does.

```lean
#check (andCommutes pfKandC)
-- Applying andCommutes to pfKandC returns a value/proof of type CandK
-- namely, CandK.intro applied to the component proofs in reverse order.
#reduce (andCommutes pfKandC)
```


## Summary

You've now seen how we can map propositions, proofs,
and the axioms of propositional logic into type theory.'
Propositions are types, proofs are values, Proofs can be
constructed and used only and exactly in ways that are
consistent with the axioms and intended meanings of the
connectives of propositional logic.

So far we've seen that a proof of a conjunction can be
defined as a pair of proofs of the individual conjuncts,
and that a proof of an implication can be given in the
form of a function, from proofs of its premise to proofs
of its conclusion.

We will now continue on down the road we're on, seeing
how, in effect, to implement the remaining connectives
(or, not, iff, etc.) as *computational* objects in type
theory.

- proofs of conjunctions are represented as pairs of proofs
- proofs of implications are represented as functions
- with lots more to come

Fun!
