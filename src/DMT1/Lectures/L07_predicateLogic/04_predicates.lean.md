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

### Domain of Application

To reduce repetition, we can abstract the variation in
these two results to a variable-valued formal parameter,
here of a type we will now call Person. Our Person type
defines just three *people* (Carter, Kevin, and Tammy).

```lean
inductive Person : Type where | Carter | Kevin | Tammy
open Person
```

### Generalization

Now we define *IsFromCville* as a predicate on people (on
terms of type Person), represented as an *inductive family*
of propositions, one for each person, with the specified
ways to prove such propositions. The proof constructors are
the introduction rules for constructing proofs of any given
proposition of this kind. Given any Person, *p*, *birthCert
p* will typecheck as proof that *p isFromCville*, and so will
*driversLicense p*.


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

### Constructing Proofs of Evenness (Introduction)

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

### Using Proofs of Evenness

We should expect to be able to use proofs of evenness
in reasoning. For example, if we have a proof that 6
is even, then we should be able to obtain from it a
proof that, say, 4 is even, we we have just seen that
sitting inside a proof term showing that 6 is even is
a proof term showing that 4 is even. The trick will be
to pattern match on the proof that 6 is even to get at
the proofs nested inside it.

```lean
example : Ev 6 → Ev 4
| (Ev.evPlus2 4 h4) => h4
```

EXERCISE: Show that if 6 is even so is 2 using this method.
Hint: Pattern match deeper into the proof of Ev 6.

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
