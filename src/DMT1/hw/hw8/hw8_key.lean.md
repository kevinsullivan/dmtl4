# Propositions as Computational Types

### Some Fundamental Types

First, we review a few fundamental types. The first
three are meant to help the reader see that there are
types with two values (Bool), one value (Unit), and no
values at all, Empty.
```lean
#check Bool
#check Unit
#check Empty
```

## Some Propositions Represented as Types

Here we define three types representing three true
propositions, P, Q, and R, and then N representing
a false proposition.
```lean
inductive P : Type where | mk deriving Repr  -- has constructor
inductive Q : Type where | mk deriving Repr  -- has constructor
inductive R : Type where | mk deriving Repr  -- has constructor
inductive N : Type where deriving Repr  -- no constructors
```

The *deriving Repr* bit just tells Lean to do some work
so that values of these types print out more nicely when
using #eval/#reduce.

## Proofs as Values of Types Representing Propositions

Can we "prove" the true ones? We prove a proposition
simply by giving Lean a "proof value" to check. Here
we first give a "proof" of P, binding the name "p" to
it. Second we give a proof of Q without binding a name.
```lean
def p : P := P.mk
example : Q := Q.mk

-- Can prove N?
def r : N := _    -- No. There's no proof term for it!

def np : P → Empty
| P.mk => _

-- Proof of ~N
def nn : N → Empty := fun n => nomatch n
```

## The Logical Connectives

We see how to represent elementary propositions, such
as *P* and *Q*, as types, with values of these types as
proofs. But what about compounding propositions such as
*P ∧ Q, P ∨ Q, P → Q, or ¬P?* We will now deal with each
of these in turn.

### Representing P ∧ Q as P × Q

We will represent the proposition, *P ∧ Q*, as the type,
*Prod P Q* in Lean. This is the type that represents all
ordered pairs of values of types *P* and *Q* respectively,
If values are proofs, then a pair with a proof of *P* as
its first value and a proof of *Q* as its second value will
suffice as a proof of P ∧ Q.

Here's Lean's definition of the polymorphic pair type in
Lean 4, enclosed in a namespace so as not to conflict with
the standard Library *Prod* type.

```lean
namespace hide
structure Prod (α : Type u) (β : Type v) where
  mk ::
  fst : α
  snd : β
end hide
```

The *Prod* polymorphic type builder  takes two types as
its arguments. For our purposes here we assume they will
represent the two propositions being conjoined. Now, by the
definition of *structure* in Lean, if one has a value, *h*,
of type *Prod P Q*, then *h.fst* is the contained proof of
*P* and *h.snd* is that for *Q*. Finally, Lean provides ×
as concrete syntactic notation for *Prod*, reflecting the
standard notion of a product of types or sets in mathematics.

Product types have one constructor with multiple arguments,
and so can only be instantiated if one has arguments of each
of the required types. The constructor of a type *Prod P Q*,
or equivalently *P × Q*, is called *Prod.mk*. So let's look
at some examples.

```lean
abbrev PAndQ := P × Q    -- Representing the proposition, P ∧ Q
def pandq : P × Q := Prod.mk P.mk Q.mk  -- Representing proof!
example : P × Q := ⟨ P.mk, Q.mk ⟩       -- Notation for Prod.mk
```


Comparing the setup we've contstructed here, we see that
the and_intro proposition, which we validated in propositional
logic, remains true here. That rule said *P → Q → P ∧ Q*. That
rule is realized in our new setup by the *Prod* constructor!
If given a value of *P* and one of *Q*, it returns a value of
*P × Q*, which, here, we're viewing as a proof of *P ∧ Q*.

Similarly, the *elimination* (elim) rules from predicate logic
work just as well here. They are *P ∧ Q → P* and *P ∧ Q → Q*.
Given a value, here a proof, *h : P × Q*, again representing
a proof of P ∧ Q, you can derive a proof of *P* as *h.fst* and
a proof of *Q* as *h.snd*. (Note: it's because Prod is defined
as a *structure* that you can use its argument names as field
names to access the component values of any such structure.)

```lean
#eval pandq.fst
#eval pandq.snd
```

Not only have we thus embedded the three "axioms" for ∧
in propositional logic into Lean 4, but we can now also
prove theorems about ∧, as defined in proposition logic
in the *identities* file.

For example, we confirmed semantically in propositional
logic, using our validity checker, that *(P ∧ Q ↔ Q ∧ P)*
is valid. Let's consider just the forward direction, i.e.,
*P ∧ Q → Q ∧ P*. For us, a proof of that is a function:
one that takes a value of type (a proof of) *P ∧ Q* as an
argument and that returns a proof of *Q ∧ P*. Using *Prod*
for ∧, what we need to show is *P × Q → Q × P*.

That we can define this function shows that if we're given
a proof (value) of *P ∧ Q* represented as a value of *P × Q*,
then we can *always* turn it into a proof of *Q ∧ P* in the
form of a value of type *Q × P*. All that we have to do in
the end is flip the order of elements of the proof of *P ∧ Q*
to get a term that will check as proof of *Q ∧ P*. Here it
is, in three equivalent versions: fully written out; using
Lean's ⟨_, _⟩ notation for the default *mk* constructor; and
finally all on one line, as an explicit function term.

```lean
-- P ∧ Q → P
example : P × Q → P := fun (h : P × Q) => h.fst
example : P × Q → P := fun ⟨ p, q ⟩  => p

def andCommutative : P × Q → Q × P
| Prod.mk p q  => Prod.mk q p

def andCommutative' : P × Q → Q × P
| ⟨ p, q ⟩ => ⟨ q, p ⟩

def andCommutative'' : P × Q → Q × P := λ ⟨ p, q ⟩ => ⟨ q, p ⟩
```

### Representing P ∨ Q as P ⊕ Q

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

```lean
#check Sum
```


`Sum α β`, or `α ⊕ β`, is the disjoint union of types `α` and `β`.
An element of `α ⊕ β` is either of the form `.inl a` where `a : α`, or `.inr b` where `b : β`.

inductive Sum (α : Type u) (β : Type v) where
  /-- Left injection into the sum type `α ⊕ β`. If `a : α` then `.inl a : α ⊕ β`. -/
  | inl (val : α) : Sum α β
  /-- Right injection into the sum type `α ⊕ β`. If `b : β` then `.inr b : α ⊕ β`. -/
  | inr (val : β) : Sum α β

```lean
-- Proof of *or* by proof of left side
def porq1 : Sum P Q := Sum.inl P.mk

-- Proof by proof of right side, with notation
def porq2 : P ⊕ Q := Sum.inr Q.mk
```

You should be able to construct your own simple examples
from here, as in the previous section, but let's go ahead
and formulate a prove as a theorem one direction of one
of the equivalences, namely *P ∨ Q → Q ∨ P*. But before we
get formal, why should this be true? How would you reason
through this? Try it on your own first, then proceed.

The trick is to see that you have to deal with two possible
cases for any given proof of *P ∨ Q*: one constructed from a
proof of *P* on the left and one constructed from a proof of
*Q* on the right. What we need to show is that *we can derive
a proof of *Q ∨ P* in either case. In the first case we can
have a proof of *P* from which we can prove *Q ∨ P* on the
*right*. In the second case we have a proof of *Q* on the
right, and from that we can prove *Q ∨ P* with that proof
of *Q* moved to the left.

```lean
example : P ⊕ Q → Q ⊕ P
| Sum.inl p => Sum.inr p
| Sum.inr q => Sum.inl q
```


### Negation as Proof of Emptiness

If a proposition, *P*, has any proofs, it must be judged
as true. So the only way represent a false proposition
is as a type with no values whatsoever. In this file, *N*
is a proposition represented as a type with no values. It
is thus false, in our view.

Now comes the fun part: Given that it's false, we would
expect ¬N to be true. We will represent the propsition,
¬N, as the function type, *N → Empty*, where *Empty* is
a standard definition in Lean of a type with no values.

The tricky underpinning of this strategy is that if a
type, say *N*, has one or more values, then no (total)
function from *N* to empty can be defined, as there will
be some value of *N* for which some value of type *Empty*
will have to be returned, but there are no such values.
It's only when *N* is empty that it will be possible to
define such a total function to *Empty.* That's because
there are *no* values/proofs of *N* for which a value of
the *Empty* type needs to be returned.

```lean
-- Can't prove that P is false, as it has a proof
def falseP : P → Empty
| P.mk => _   -- can't return value of Empty type!


-- But *N* is empty so this definition works
def notr : N → Empty := fun r => nomatch r
```

The upshot of all of this is that we can prove that
a proposition, say *N*, is false by proving that it
has no proofs, and we do that by proving that there
*is* a function from that type to Empty. We can even
define a general purpose *neg* connective to this end,
and give it a concrete notation, such as *~*.

```lean
def neg (A : Type) := A → Empty
notation: max "~"A => neg A
example : ~N := λ h => nomatch h
```

## Summing Up

With that, we've embedded most of the propositional
part of predicate logic into Lean, and are now able
to write (and even prove) interesting propositions.
Here's a last example before you set off on your own
homework. We'll prove P ∧ (Q ∨ R) → P ∧ Q ∨ P ∧ R.
Notice that we *must* do a case analysis to deal
the the disjunction.


```lean
-- P ∧ (Q ∨ R) → (P ∧ Q ∨ P ∧ R)
example : P × (Q ⊕ R) → (P × Q ⊕ P × R)
| Prod.mk p (Sum.inl q)  => Sum.inl (Prod.mk p q)
| ⟨ p, Sum.inr r ⟩ => Sum.inr ⟨ p, r ⟩ -- w/ notation
-- you write the second missing case
```

## Homework

Write and prove the following propositions from the
identities file in the propositional logic chapter.
Use the space below. If you ever get to the point where
you're sure there's no possible proof, just say so and
explain why. Use ×, ⊕, and ~ as notations for logical
and, or, and not when translating these propositions
into our current embedding of predicate logic in Lean
(just as we did in the preceding example).

- P ∧ (Q ∧ R) → (P ∧ Q) ∧ R   -- and is associative
- P ∨ (Q ∨ R) → (P ∨ Q) ∨ R   -- or is associative


- ¬(P ∧ Q) → ¬P ∨ ¬Q
- ¬(P ∨ Q) → ¬P ∧ ¬Q
- ¬(P ∧ N)
- (P ∨ N)


```lean
/-
One of the  valid theorems of proposition logic
is this part of one of DeMorgan's Laws explaining
how negation distributes over conjunctions.
-/
-- ¬(P ∧ Q) → (¬P ∨ ¬Q)
example : (~(P × Q)) → (~P) ⊕ (~Q) :=
    -- assume (P ∧ Q) → Empty
    -- show P → Empty
  fun (h : ~(P × Q)) =>
    Sum.inr _
```

At this point we're stuck. In constructive logic,
just knowing that P ∧ Q is false is not enough to
give you a proof of either ¬P or of ¬Q. This is an
example of a theorem in propositional logic (valid)
that is not valid in the constructive logic of Lean.

What about in the other direction?

```lean
example: (~P) ⊕ (~Q) → (~(P × Q)) :=
fun (h : (~P) ⊕ ~Q) =>
  fun pandq =>
    match h with
    | Sum.inl np => np pandq.fst
    | Sum.inr nq => nq pandq.snd


/- HOMEWORK 9!
The other of DeMorgan's laws explains how negation
distributes over disjunctions. In the forward direction
it proposes that if you know what P or Q is false, which
means neither is true, then at least one of them must be
false. Classically that makes sense. Is this theorem of
propositional logical also valid in Lean?
-/

-- ¬(P ∨ Q) -> ¬P ∧ ¬Q

example : (~(P ⊕ Q)) -> (~P) × (~Q) :=
fun (h : (~(P ⊕ Q))) =>
  _

example : (~P) × (~Q) → (~(P ⊕ Q)) :=
_
```

In classical logic we know it's false that both P
and ¬P are true. Is that also true in constructive
logic? Prove it if you can.
```lean
example : ~(P × (~P)) := _
```

What about the axiom of negation elimination? That is,
¬¬P ↔ P. Is it valid in both directions, one direction,
or neither?

```lean
example : P → (~(~P)) :=
λ p => fun np => _
```

Ok, so, even in constructive logic, from a proof of
P we can derive a proof of ¬¬P. How about in the other
direction?
-/
example : (~(~P)) → P :=
_
