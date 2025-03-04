# Predicates

<!-- toc -->

In this chapter and from now on we'll be working with Lean's
standard embedding of predicate logic, with propositions encoded
as types of the Prop (rather than Type) sort. But let's start with
the even more basic question, *what is a predicate?*

A predicate in a predicate logic is a proposition parameterized
in a way that lets it speak about different objects: those that
can be filled in for these placeholders.

If *KisFromCville* and *CisFromCVille* are both propositions, for
example, represented in Lean by types of these names in Prop, with
analogous proof terms, then we can factor out *person* as subject
to variation, as a parameter. The proposition, in Prop, becomes a
function, of type Person → Prop, that when applied to a particular
person yields the original proposition *about* that person.

## Example: Being From Charlottesville

Our example postulates a few different people, two of whom are
from Charlottesville (CVille) and one of whom is not.

### Propositions as Types

Here are types in Prop representing two propositions, each
coming with the same two constant proof/constructor terms.
Informally, someone is proved to be from CVille if they have
a birth certificate or drivers license that says so.

```lean
inductive KevinIsFromCville : Prop where
| birthCert
| driversLicense

inductive CarterIsFromCville : Prop where
| birthCert
| driversLicense
```

### Domain of Discourse

To reduce repetition, we can abstract the variation in
these two results to a formal parameter to be bound to a
person: a terms of a Person type. The Person type here
defines just three *people* (Carter, Kevin, and Tammy).

```lean
inductive Person : Type where | Carter | Kevin | Tammy

open Person
```

### Generalization

Now we define IsFromCville as an *inductively defined*
predicate. This type builder takes a Person term as an
argument and reduces to a propositions (about that person
being from Cville). The constructors then define the terms
of this type. Given any person, *p*, *birthCert p* will
typecheck as proof that *p isFromCville*, and similarly
for driversLicense.


```lean
-- Generalization: proposition that <p> is from CVille
inductive IsFromCville : Person → Prop where
| birthCert       (p : Person) : IsFromCville p
| driversLicense  (p : Person) : IsFromCville p
open IsFromCville
```

### Specialization

Whereas abstraction replaces concerete elements with placeholders,
specialization fills them in with particulars. Given a predicate,
we *apply* it to an actual parameter to fill in missing information
for that argument. We apply a *universal*, over all people, to any
particular person, to *specialize* the predicate to that argument.

```lean
#check IsFromCville Kevin   -- specialization to particular proposition
#check IsFromCville Carter  -- pronounce as "Carter is from Cville"
#check IsFromCville
```

### Proofs

We can now see how to "prove" propositions obtained by applying
predicates to arguments. You apply IsFromCville a Person, it gives
you back a proposition. In addition, as an inductive type, it gives
a set of constructors for proving such propositions. The following
code defines pfKevin and pfCarter as proofs of our propositions.
```lean
def pfKevin : IsFromCville Kevin := birthCert Kevin
def pfCarter : IsFromCville Carter := driversLicense Carter
```

### Summary
So there! We've now represented a *predicate* in Lean, not
as a type, per se, but as a function that takes a Person as
an argument, yields a proposition/type, and provies general
constructors "introduction rules" for contructing proofs of
these propositions.

## The Property of a Natural Number of Being Even

As another example, we define a very different flavor of
predicate, one that applies not to people but the numbers,
and that indicates not where one is from but whether one is
even or not. This is an *indictive* definition, in Prop, of
the recursive notion of evenness. It's starts with 0 being
even as a given (constant constructor), and the includes an
indictive constructor that takes any number, *n*, and proof
that it is even and wraps it into a term that type checks as
a proof that *n+2* is even. Note that term term accepted as
a proof that *n+2* is even has embedded within it a proof
that *n* is even. These recursives structures always bottom
out after some finite number of steps with the proof that 0
is even. Note that we have Ev taking numbers to propositions
*in Prop.*

```lean
inductive Ev : Nat → Prop where
| evZero : Ev 0
| evPlus2 : (n : Nat) → Ev n → Ev (n + 2)
open Ev
```

## Proofs of Evenness

And here (next) are some proofs of evenness:
- 0 is even
- 2 is even
- 4 is even
- 6 is even (fully expanded)

```lean
def pfZeroEv : Ev 0 := evZero
def pfTwoEv : Ev 2 := evPlus2 0 pfZeroEv
def pfFourEv : Ev 4 := evPlus2 2 pfTwoEv

-- hint: find the base proof then read this inside out
def pfSixEv : Ev 6 :=
  evPlus2
    (4)
    (evPlus2      -- proof that 4 is even
      (2)
      (evPlus2    -- proof that 2 is even
        (0)
        evZero    -- constant proof that 0 is even
      )
    )
```

### Proofs of Negations of Evenness

Why can't we build a proof that 5 is even?
Well, to do that, we'd need a proof that 3
is even, and for that, a proof that 1 is even.
But we have no to construct such a proof. In
fact, we can even prove that an odd number (we
might as well just start with 1) is *not* even
in the sense defined by the *Ev* predicate.

```lean
example : ¬Ev 1 :=
```
Recall: ¬Ev 1 is defined to be (Ev 1 → False).
To prove ¬Ev 1 we need a function of this type.
Applied to a proof Ev 1, it return a proof a False.
Read it out loud: *if* Ev 1 then False, with the
emphasis on if. But Ev 1 is not true, it's false,
so the entire implication is true as explained by
the fact that it's true for *all* proofs of Ev 1
(of which there are none).A  total function from
an uninhabited type to any other type is trivial.
Here, it's:
```lean
fun (h : Ev 1) => nomatch h

example : ¬Ev 1 := fun (h : Ev 1) => nomatch h
example : ¬Ev 3 := fun (h : Ev 3) => nomatch h
example : ¬Ev 5 := fun (h : Ev 5) => nomatch h
```

### Generalization over Empty Set (of Proofs)

Any proopsition quantified universally over an
empty set or type is valid, because it's true for
all values in that set or type, and because there
are none, in particular.

Another way to see that this makes sense is to view
universal quanitification as logical conjunction of
the family of propositions generated by the predicate
on the right specialized to a proposition about each
partixular value in the set or type.

The generalized conjunction of such a paramterized
family of propositions could be thought of as being
computed by recursion. With more than zero terms, you
take the conjunction of the first time with the result
of aplying this procedure to the rest. To preserve the
result when finally combining it with the answer in the
case where there are zero conjuncts to conjoin, the result
for the empty case has to be *true*. Yet another way to
see it: *true* is both a left and right identity element
for logical (truth-functional) *And*. You should check
your undertsanding by finishing this proof that True *is*
both a left and a right identity element for *And*.

### Aside: True is the Identity Element for ∧

```lean
theorem leftRightIdentityAndTrue :
```
Note quantification over all propositions. So now we're
seeing that it makes eminent sense to express ideas at a
level of generality not expressible in first-order theory.
But here we have captured exactly the abstraction that we
want. You can finish the proof here that True really is an
identity, both left and right, for any proposition.
```lean
∀ (P : Prop),
  ((P ∧ True) ↔ P) ∧
  ((True ∧ P) ↔ P)
:=
fun (p : Prop) =>
  And.intro
    (Iff.intro
      (fun h => h.left)
      (fun h => ⟨ h, True.intro⟩))
    (sorry)
```
