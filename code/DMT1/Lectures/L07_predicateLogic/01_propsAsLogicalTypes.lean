/- @@@
# Propositions as Logical Types

<!-- toc -->

In the previous chapter, we saw that we could represent
propositions as *computational types*, and proofs of them
as various programs and data structures. Reasoning is thus
reduced to programming!

However, there are some problems with the approach so far:

- it doesn't distinguish logical from computational types
- it enables one to distinguish between proofs of propositions

What we would like, then, is to have a slightly different sort
of type, differing from the usual data types in these two ways:

- connectives can only accept types representing *propositions*
- the choice of a proof to show validity is entirely irrelevant
- and of course we'd like to use the usual logical notations

To this end, Lean and similar logics define a new sort of type,
called *Prop*, dedicated to the representation of propositions,
and having these additional properties.

In this chapter, we run through exactly the same examples as
in the last, but now using Prop instead of Type as the type
of propositions.
@@@ -/

/- @@@
## Types in Prop Replace Types in Type

We can represent elementary propositions, and their truth or
falsing, by defining types that either do or do not have any
values. Here we define three ropositions, *P, Q, R,* each of
which has a proof term, and one proposition, *N*, that has no
constructors and thus no proofs, and which we would thus judge
to be false.
@@@ -/

inductive P : Prop  where | mk
inductive Q : Prop  where | mk
inductive R : Prop  where | mk
inductive N : Prop  where


/-@@@
## (False : Prop) Replaces (Empty : Type)

In Lean, *False* is represented as an uninhabited type in Prop.
Be sure to visit the definition of *False* to see that it's just
like *Empty* except that it's a "reasoning" type rather than a
*computational* type (such as *Bool → Empty*).
@@@ -/

#check Empty
#check False
-- inductive False : Prop

/- @@@
### Introduction

As there can be no proof of *False*, there is no introduction rule
for it. In Lean that means it has no constructors. The only way to
derive a proof of *False* is if one is in a context in which one has
already made conflicting assumptions. In the following example, you
can see that from the inconsistent assumption, *1 = 0*, we can derive
a proof of False.
@@@ -/

example : 0 = 1 → False :=
  fun h =>
    let (f : False) := nomatch h
    -- this example continues below

/- @@@
Now having derived a proof of false, from our inconsistent
assumption, we can use the axiom of false elimination (*False.elim*
in Lean) to succeed≥ The underlying reasoning is that *we are in a
a situation that can never actually occur -- you can never have a
proof of *1 = 0 to pass as an argument* -- so we can just ignore
reasoning any further in this situation and declare success.
@@@ -/

    -- Here then is the last line of the proof
    False.elim f

/-@@@
## (True : Prop) replaces (Unit : Type)

*True* in Lean is a proposition, a logical reasoning type,
analogous to the computational type, *Unit*, but in *Prop*.
@@@ -/

#check Unit
#check True

/- @@@
### Introduction

There's always a constant (unconditional) proof of *True*,
as the constructor, *True.intro*. There's always a proof of
*True*.

### Elimination

There's nothing useful one can do with a proof of True other
than to signal that a computation has completed. There's thus
no really useful elimination rule for true. Exercise: explain
what the recursor/induction axiom says about it.
@@@ -/
#check True.rec


/- @@@
## Proofs Are Now Values of "Reasoning" Types

We continue to represent proofs as values of a given type,
and we can use Lean to check that proofs are correct relative
to the propositions they mean to prove. It's just type checking!
We do have a new keyword available: *theorem*. It informs the
reader explicitly that a value is intended as a proof of some
proposition.
@@@ -/

def p' : P := P.mk
example : Q := Q.mk
theorem p : P := P.mk

/- @@@
The same principles hold regard false propositions represented
as types. They are *logical* types with no proofs. Therefore you
can't prove them in Lean.
@@@ -/
theorem r : N := _    -- No. There's no proof term for it!

/- @@@
## And and Or Connectives Are Polymorphic Types (in Prop)

Lean 4 defines separate logical connectives just for types
in Prop.

### Replace (P × Q) with (P ∧ Q)

Here as a reminder is Lean's definition of the polymorphic
pair type in Lean 4, followed by its definition of *And*.
@@@ -/

#check And

namespace hide

structure Prod (α : Type u) (β : Type v)  where
  mk ::
  fst : α
  snd : β

structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b

end hide

/- @@@
We now make the following replacements:

- replace × with ∧
- replace Prof.mk with And.intro
- replace Prod.fst and Prod.snd with And.left and And.right
@@@ -/

#check P
#check @And

abbrev PAndQ : Prop := P ∧ Q    -- Representing the proposition, P ∧ Q
theorem pandq : P ∧ Q := And.intro P.mk Q.mk  -- Representing proof!
example : P ∧ Q := ⟨ P.mk, Q.mk ⟩       -- Notation for Prod.mk


/- @@@
@@@ -/

#check pandq.left
#check pandq.right

/- @@@
@@@ -/

/- @@@
All of the usual theorems then go through as before.
Here we're actually seeing the form of a proof of an
*implication* in type theory: and it's a function from
proof of premise to proof of conclusion.
@@@ -/

def andCommutative : P ∧ Q → Q ∧ P
| And.intro p q  => And.intro q p

def andCommutative' : P ∧ Q → Q ∧ P
| ⟨ p, q ⟩ => ⟨ q, p ⟩

def andCommutative'' : P ∧ Q → Q ∧ P := λ ⟨ p, q ⟩ => ⟨ q, p ⟩

/- @@@

### Replace P ⊕ Q (Sum Type) with P ∨ Q

As we represented the conjunction of propositions as a
product type, we will represent a disjunction as what is
called a *sum* type. Whereas a product type has but one
constructor with multiple arguments, a sum types has two
constructors each taking one argument. A value of a product
type holds *one of these and one of those*, while a sum
type holds *one of these or one of those*. We thus used
the polymnorphic *Prod* type to represent conjunctions,
and now we do the same, using the polymorphic Sum type to
represent disjunctions and their proofs.
@@@ -/

#check Sum
#check Or


/- @@@ OR AS SUM

inductive Sum (α : Type u) (β : Type v) where
  | inl (val : α) : Sum α β
  | inr (val : β) : Sum α β


inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b
@@@ -/

def porq := P ∨ Q

-- Proof of *or* by proof of left side
def porq1 : Or P Q := Or.inl P.mk

-- Proof by proof of right side, with notation
def porq2 : P ∨ Q := Or.inr Q.mk

/- @@@
All the theorems from before also go through just fine.
@@@ -/

example : P ∨ Q → Q ∨ P
| Or.inl p => Or.inr p
| Or.inr q => Or.inl q



/- @@@
## Implications Are Represented as Function Types

Implications continue to be represented by function types.

To prove an implication, we simply exhibit a function of
the specified type. Such functions might not exist, and in
the case that would show the implication to be false. On the
other hand, *any* function definition of the given type will
do to prove an implication.

### Introduction

Here for example we prove the implication stating that if
both P and Q are true then P is. The reasoning is just as
before: assume we're given a proof of P ∧ Q, and from it,
derive a proof of P. That shows that it P ∧ Q is true then
so much be P.
@@@ -/

def pandQImpP : P ∧ Q → P := fun (h : P ∧ Q) => h.left


example (A : Prop) : False → A := fun f => nomatch f



/- @@@
### Elimination

To *use* a proof of an implication, we just *apply* it,
as a function, to an argument of the right type. It will
ll then reduce to term that will serve as a proof of the
conclusion of the implication.

In other words, the way to *use* a proof of an implication
is to apply it. Function application is the elimination rule
for proofs of implications. Such proofs *are* in the form of
functions. Here we show that if we assume we have a proof of
*P ∧ Q → P* and we have a proof of *P ∧ Q* then we can derive
a proof of *P* by applying the former to the latter.
@@@ -/

example (P Q : Prop) : (P ∧ Q → P) → (P ∧ Q) → P :=
λ pq2p pq => (pq2p pq)

-- Test yourself: what are the types of pq2p and pq?

/- @@@
## Negations Are Represented as Function Types to False

Negation is the most complex of the connectives that we
have seen so far. First, we represent a propostion, *¬P*
as the function type, *P → False*, where *False* is Lean's
standard *empty* (uninhabited) reasoning type.

### Introduction

To prove a negation, such as the proposition, *¬P*, we
assume *P*, show that that leads to a contradiction, in
the sense that it's shown that there can be no proof of
*P*. That proves *P → False*. The negation introduction
axiom then let's us conclude *¬P*.
@@@ -/

-- You can prove a falsehood
def oneNeZero : ¬(1 = 0) := fun (h : 1 = 0) =>
  let f : False := nomatch h
  False.elim f

-- It's not true that P is false, as defined above
example : P → False
| P.mk => _   -- can't return value of Empty type!


-- But *N* is empty so this definition works
def notr : N → False := fun r => nomatch r

/- @@@
### Elimination

A proof of a negation is a special case of a proof of an
implication. Both proofs are in the form of *functions*.
The way we *use* a proof of a negation, as with a proof
of any implication, is by applying it. This is generally
done in the *context of conflicting assumptions* that let
us derive a proof of false. In Lean one then generally
uses *False.elim*
@@@ -/

def noContra (A B : Prop) : A → ¬A → B :=
λ (a : A) (na : ¬A) => (na a).elim


/- @@@
## Summing Up

In class exercise. Take this example from last time
and fix it to use Prop.
@@@ -/

example : P ∧ (Q ∨ R) → (P ∧ Q ∨ P ∧ R)
| ⟨ p, Or.inl q ⟩ => Or.inl ⟨ p, q ⟩
| ⟨ p, Or.inr r ⟩ => Or.inr ⟨ p, r ⟩
-- you write the second missing case


/- @@@
- ∧
- ∨
- ¬
- →
- ↔
@@@ -/

#check Iff

/- @@@
structure Iff (a b : Prop) : Prop where
  intro ::
  mp : a → b
  mpr : b → a
@@@ -/

-- our example is set up so that we have proofs of P and Q to return
example : P ↔ Q := Iff.intro (fun _ : P => Q.mk) (fun _ : Q => P.mk)

/- @@@
Universal quantifier
@@@ -/

def allPQ : ∀ (_ : P), Q := fun (_ : P) => Q.mk
-- P → Q
-- Wait, what?

-- Hover over #reduce.
#reduce ∀ (p : P), Q
-- (∀ (p : P), Q) literall *is* P → Q

/- @@@
So that's our first taste of the two quantifiers of a
predicate logic: *for all* (∀) and *there exists* (∃).
What we've seen here is a special case of the more general
form of a universally quantified proposition.

To see the general form of quantified propositions, we now
need to meet predicates: as a concept, and as that concept
is embedded (very naturally) in Lean. That takes us into the
next chapter, on *predicates*.
@@@ -/


/-@@@
## Homework

Write and prove the following propositions from the
identities file in the propositional logic chapter.
Use the space below. If you ever get to the point where
you're sure there's no possible proof, just say so and
explain why. Use the standard logical notations now,
instead of the notations for Prod and Sum. That is,
just use the standard logical notations in which the
propositions are written here.

- P ∧ (Q ∧ R) → (P ∧ Q) ∧ R   -- and associative (1 way)
- P ∨ (Q ∨ R) → (P ∨ Q) ∨ R   -- or associative (1 way)
- ¬(P ∧ Q) → ¬P ∨ ¬Q
- ¬(P ∨ Q) → ¬P ∧ ¬Q
- ¬(P ∧ N)
- (P ∨ N)
@@@ -/

-- Your answers here
