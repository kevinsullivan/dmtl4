/- @@@
# Propositions as Types

<!-- toc -->

By the term, *computational types*, we mean types of data
that are designed to support computations on ordinary data.

The purpose of this chapter is to see that "no new magic" is
needed to represent propositions as types, with their proofs
being their values, using ordinary computational types.
@@@ -/

/-@@@
## Some Fundamental Computational Types

First, we review a few fundamental types. The first
three are meant to help the reader see that there are
types with two values (Bool), one value (Unit), and no
values at all, Empty. In VSCode you can right click on
the type names and select *go to definition* to visit
the definitions of these types in Lean's libraries. You
know how to read this kind of code now.
@@@ -/

#check Bool
#check Unit
#check Empty

/- @@@
## Set-Up for Running Example

We can represent elementary propositions, and their truth or
falsing, by defining types that either do or do not have any
values. Here we define three true propositions, *P, Q, R,* and
one false one, *N*, the negation of which will then be true.
@@@ -/
inductive P : Type  where | mk deriving Repr  -- has value
inductive Q         where | mk deriving Repr  -- has value
inductive R         where | mk deriving Repr  -- has value
inductive N         where /-nothing!-/ deriving Repr  -- no values

/- @@@
Lean Detail: The *deriving Repr* annotation simply asks Lean to
generate code to pretty print values of the given type, e.g., when
one uses #eval/#reduce to produce a reduced value to be displayed.
@@@ -/

/- @@@
## Proofs are Values of "Logical" Types

One of the powers of Lean is that it checks proofs for deductive
correctness. In practice we'll gnerally
accept taht a proposition is true if there's any proofs of it.
But with proofs as values, that means that all we have to do is
have Lean check that we've given it a value of the right type.


We have been doing this fromt the start with *def* in Lean. It
binds a name/identifier, *p*, to a value of type *P*, here to
*P.mk.* The point here is that Lean typechecks such bindings.
When proofs are values, it's Lean's typechecker that assures
that only correctly constructed values will typecheck as proofs.
The example construct forces typechecking but without binding a
name.
@@@ -/

def p : P := P.mk
example : Q := Q.mk

/- @@@
Now recall that we've represented the false proposition, N,
as a type with no proof terms. If we try to prove *N* by
giving Lean a term to typecheck, we get stuck, because there
is no such term, as we defined *N* to be an empty type. It's
good news that we can't prove *N* is true, as we've meant
from the beginning for it to be false. What we haven't yet
got is the idea of negation, and that the negation of false
shold be true.
@@@ -/
def r : N := _    -- No. There's no proof term for it!

/- @@@
## The Logical Connectives

We see how to represent elementary propositions, such
as *P* and *Q*, and *N*m as types. But what about
compound propositions such as *P ∧ Q, P ∨ Q, P → Q,*
or *¬P?* We will now show how the logical connectives
are embedded in Lean.

### Representing P ∧ Q as P × Q (Product Types)

We will represent the proposition, *P ∧ Q*, as the type,
*Prod P Q* in Lean. This is the type that represents all
ordered pairs of values of types *P* and *Q* respectively,
If values are proofs, then a pair with a proof of *P* as
its first value and a proof of *Q* as its second value will
suffice as a proof of P ∧ Q.

Here's Lean's definition of the polymorphic pair type in
Lean 4, enclosed in a namespace so as not to conflict with
the standard Library *Prod* type.
@@@ -/

namespace hide
structure Prod (α : Type u) (β : Type v) where
  mk ::
  fst : α
  snd : β
end hide

/- @@@
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
@@@ -/

abbrev PAndQ := P × Q    -- Representing the proposition, P ∧ Q
def pandq : P × Q := Prod.mk P.mk Q.mk  -- Representing proof!
example : P × Q := ⟨ P.mk, Q.mk ⟩       -- Notation for Prod.mk


/- @@@
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
@@@ -/

#eval pandq.fst
#eval pandq.snd

/- @@@
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
@@@ -/

/- @@@
That we can define this function shows that if we're given
a proof (value) of *P ∧ Q* represented as a value of *P × Q*,
then we can *always* turn it into a proof of *Q ∧ P* in the
form of a value of type *Q × P*. All that we have to do in
the end is flip the order of elements of the proof of *P ∧ Q*
to get a term that will check as proof of *Q ∧ P*. Here it
is, in three equivalent versions: fully written out; using
Lean's ⟨_, _⟩ notation for the default *mk* constructor; and
finally all on one line, as an explicit function term.
@@@ -/

def andCommutative : P × Q → Q × P
| Prod.mk p q  => Prod.mk q p

def andCommutative' : P × Q → Q × P
| ⟨ p, q ⟩ => ⟨ q, p ⟩

def andCommutative'' : P × Q → Q × P := λ ⟨ p, q ⟩ => ⟨ q, p ⟩

/- @@@

### Representing Sum P Q (P ⊕ Q) with Or P Q (P ∨ Q)

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


/- @@@ OR AS SUM
`Sum α β`, or `α ⊕ β`, is the disjoint union of types `α` and `β`.
An element of `α ⊕ β` is either of the form `.inl a` where `a : α`, or `.inr b` where `b : β`.

inductive Sum (α : Type u) (β : Type v) where
  /-- Left injection into the sum type `α ⊕ β`. If `a : α` then `.inl a : α ⊕ β`. -/
  | inl (val : α) : Sum α β
  /-- Right injection into the sum type `α ⊕ β`. If `b : β` then `.inr b : α ⊕ β`. -/
  | inr (val : β) : Sum α β
@@@ -/

-- Proof of *or* by proof of left side
def porq1 : Sum P Q := Sum.inl P.mk

-- Proof by proof of right side, with notation
def porq2 : P ⊕ Q := Sum.inr Q.mk

/- @@@
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
@@@ -/

example : P ⊕ Q → Q ⊕ P
| Sum.inl p => Sum.inr p
| Sum.inr q => Sum.inl q





/- @@@
### Implication as Function Type

We can now represent a logical implication, *P → Q* as
the corresponding total function type, *P → Q*, viewing
*P* and *Q* now as types. Indeed, they are the types of
their proofs. So *P → Q* is a type, namely the type of a
function that takes any proof of *p* as an argument and
and from it derives and finally returns a proof of Q. So
if *P* is true, this function can then that so is *Q*,
@@@ -/





/- @@@
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
@@@ -/

-- Can't prove that P is false, as it has a proof
def falseP : P → Empty
| P.mk => _   -- can't return value of Empty type!


-- But *N* is empty so this definition works
def notr : N → Empty := fun r => nomatch r

/- @@@
The upshot of all of this is that we can prove that
a proposition, say *N*, is false by proving that it
has no proofs, and we do that by proving that there
*is* a function from that type to Empty. We can even
define a general purpose *neg* connective to this end,
and give it a concrete notation, such as *~*.
@@@ -/

def neg (A : Type) := A → Empty
notation: max "~"A => neg A
example : ~N := λ (h : N) => nomatch h

/- @@@
## Summing Up

With that, we've embedded most of the propositional
part of predicate logic into Lean, and are now able
to write (and even prove) interesting propositions.
Here's a last example before you set off on your own
homework. We'll prove P ∧ (Q ∨ R) → P ∧ Q ∨ P ∧ R.
Notice that we *must* do a case analysis to deal
the the disjunction.
@@@ -/

example : P × (Q ⊕ R) → (P × Q ⊕ P × R)
| ⟨ p, Sum.inl q ⟩ => Sum.inl ⟨ p, q ⟩
| ⟨ p, Sum.inr r ⟩ => Sum.inr ⟨ p, r ⟩

/-@@@
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

@@@ -/

-- Your answers here


/- @@@
## Extra Credit

Not all of the axioms that are valid in propositional
logic are valid in our embedding of constructive logic
into Lean. One that's not is negation elimination: that
is, *¬¬P → P*. Try to prove it in the stype we've used
here here and explain exactly where things go wrong (in
a comment).
-/
