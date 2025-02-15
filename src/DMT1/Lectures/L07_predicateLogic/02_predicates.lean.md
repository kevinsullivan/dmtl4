# Proposition, Predicate, and Connective Types

<!-- toc -->



## Predicates
Last time we developed two examples where we represented
propositions as types.  We then noticed that these two
propositions are identical except for the "person" that they
"speak about." In particular, each of the two propositions
has exactly the same value/proof constructors. independent
of the person in question. What we will do in this section
is to *generalized* from the two specific propositions to a
single *predicate*.

### Review

Recall that a predicate is a *parameterized* proposition.
The parameters are in effect placeholders in the definition
of a proposition. When filled in with values of the right
types, predicates return propositions (represented as types
in type theory).

Here are the two original propositions.

```lean
-- Kevin is from Charlottesville
inductive KevinIsFromCville : Type where                            -- proposition as a type
| cvilleBirthCert                                   -- a proof as a value
| cvilleDriversLicense                              -- another proof
| cvilleUtilityBill                                 -- a third proof

-- Proposition: Carter is from Charlottesville
inductive CarterIsFromCville : Type where
| cvilleBirthCert
| cvilleDriversLicense
| cvilleUtilityBill
```

### Generalizing from Instances by Parameterization

Now what we want to do is to formulate a single predicate
exactly like each of these definitions but with the names
replaced by a single argument specifying the "person" that
the resulting proposition "is about." For that we will need
a new type: a Person type, whose values we will interpret
as representing individual people in the real world.

```lean
-- First, we need a Person type
inductive Person : Type where
| Kevin
| Tammy
| Carter

open Person
```

And now we can write our *generalized* predicate. We will
call it IsFromCharlottesville. On the first line, below, we
specify this name and the fact that it refers to *function*
that takes a person as an argument and that returns a *type*
that (1) represents a proposition about a particular person,
(2) comes with a collection of constructors for creating
proofs/values of such a proposition/type.

```lean
inductive IsFromCville : Person → Type where
| cvilleBirthCert (p : Person) : IsFromCville p
| cvilleDriversLicense (p : Person) : IsFromCville p
| cvilleUtilityBill (p : Person) : IsFromCville p

open IsFromCville
```

As we'e emphasized before, a predicate is a function
from arguments to propositions, where propositions are,
yet again, represented as *types*, and where proofs of
such propositions are represented as values of such
types.
```lean
#check IsFromCville
```

### Specializing to Propositions By Application to Parameter Values

Applied to arguments a predicate yields a proposition. In
Lean, we represent propositions as types. So here we are
defining propositions called KIFC and CIFC.
```lean
def KIFC : Type := IsFromCville Kevin
def CIFC : Type := IsFromCville Carter
```

## Proving Propositions Derived from Predicates

Finally we can now see how to "prove" propositions derived from
predicates represented as "inductive type builders." You give
IsFromCville a Person, it gives you not only a proposition about
that person, but the rules for constructing proofs of *any* such
proposition. The following code declares KIFC and CIFC as proofs
of our two propositions, using the same proof/value constructors
in both cases, as they're common to *all* specializations of the
given predicate.
```lean
def pfKevin : IsFromCville Kevin := cvilleBirthCert Kevin
def pfCarter : CIFC := cvilleUtilityBill Carter
```

So there! We've now represented a *predicate* in Lean, not
as a type, per se, but as a function that takes a Person as
an argument, yields a proposition/type, and provies general
rules (constructors) for building proofs.

### Another Example

We can prove that natural number is "Even" (a predicate!) by
showing that it's either zero or two more than any other even
number. Let's see an Even predicate represented in Lean in the
manner we just introduced.

```lean
inductive Ev : Nat → Type where
| pfZero : Ev 0
| pfEvPlus2 : (n : Nat) → Ev n → Ev (n+2)

open Ev
```

And here are some proofs of evenness

```lean
def pfZeroEv : Ev 0 := pfZero
def pfTwoEv : Ev 2 := pfEvPlus2 0 pfZeroEv
def pfFourEv : Ev 4 := pfEvPlus2 2 pfTwoEv

def pfSixEv : Ev 6 :=
  pfEvPlus2
    (4)
    (pfEvPlus2
      (2)
      (pfEvPlus2
        (0)
        (pfZero)
      )
    )
```


Why can't we build a proof that 5 is even?
Well, to do that, we'd need a proof that 3
is even. Why can't we build that? Well, we'd
need a proof that 1 is even. And we have no
way at all to construct such a proof. There
just isn't one given the construtors that we
have to work with.

## Logical Connectives

Ok, so now we know how to represent propositions
as types, where values are interpreted as proofs.
We also now know how to represent *predicates* as
parameterized types. But given our "propositions
as types" approach, how can we represent logical
connectives such as *And*, or *Or*?

Think about it. What does And do? It's a binary
operation. It takes two propositions and yields
a new proposition. The idea, then, is to define
*And* (and similarly for most other connectives)
as a type *parameterized* not by a data value,
such as a person or natural number, but by two
other propositions (represented as types!), with
proof construction rules that reflect precisely
what we *mean* by "And:" namely that we can get
a proof of *And P Q* if and only if we provide
proofs of P and of Q, respectively, as arguments
to an "and_intro-like" constructor. We'll call
our connective MyAnd to avoid conflicting with
And, already built into Lean.

```lean
inductive MyAnd : (P : Type) → (Q : Type) → Type where
| intro (p : P) (q : Q) : MyAnd P Q
```

It's tremendously important that you be able to
read, understand, and explain "what's going on"
with the intro constructor. What is says, in
English, is that if you apply MyAnd.intro to a
*proof (value)* of the proposition (type), P,
and to a proof of Q, then you get back a proof
(value) of the proposition (type) (MyAnd P Q),
that is, of what we'd usually write as P ∧ Q.

Now, finally, we've enabled the construction of
proofs of our own "And" expressions.

```lean
-- let nothFromCville be an "And" propopsition
def bothFromCville : Type :=
  MyAnd (IsFromCville Kevin) (IsFromCville Carter)

-- we can construct a proof of it using MyAnd.intro
def pfBothFromCville : bothFromCville :=
  MyAnd.intro sorry sorry

-- and we can of course also implement elim rules

def myAnd_elim_left : (P : Type) → (Q : Type) → (MyAnd P Q) → P
| P, Q, (MyAnd.intro p q) => p

def myAnd_elim_right : (P : Type) → (Q : Type) → (MyAnd P Q) → Q
| P, Q, (MyAnd.intro p q) => q
```
