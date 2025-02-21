/- @@@
# Introduction

<!-- toc -->

In predicate logic, whether first- or higher-order (as we
discuss later), one speaks of worlds characterized in terms
of entities (and in some predicate logics types of entities);
functions *in the world* that take and return entities; and
relations over objects represented by predicates. A predicate
in turn is simply a proposition with placeholders (parameters)
where specific objects can be plugged in to yield a proposition
about them that in turn could be judged as either true or false.
We say that an object or a tuple of objects *satisfies* a given
predicate (is *in* the relation it specifies) when the resulting
proposition about them is true. Predicate logics also support set
theory: sets of objects and ways of speaking about *all* of
the elements in a given set, or *at least one* element of a
given set as satisfying some condition.

## Overview

Predicate logic  provides syntactic symbols to refer to such
things, including *constant* and *variable* symbols (to refer
to domain entities)); *function* names, referring to functions
in the domains; and *predicate* names referring to *properties*
of individual objects, or to *relations* among entities.

Prredicate logic adopts the logical operators and their usual
truth-functional meanings from propositional logic, but now as
composing smaller expressions in predicate logic.

## Examples

We'll consider two examples.

### A String Length Property

- character strings and natural numbers as *entities*
- a *set* of strings, e.g., containing three particular strings
- a *function*, called *length*, from any string to its length
- a relation, lexicographic less than or equal, on strings

Using this vocabulary we might then want to express the
idea that *all of the strings in the set have the same length*,
In the real predicate-logic-speak we would say that there is
some natural number, n, such that n is the length of the first
string, and of the second string, and of the third string in
the set.

But rather than enumerating thos three explicitly (because,
what if it were a million of them) we'll just use a universal
("for all") quantifier. The ∀ quantifier can be thought of as
a generalized (n-ary) and (∧) operation. Thus, there is some
n such that n is the length of every string in the set of them.

```lean
∃ (n : Nat), (∀ s ∈ strings), s.length = n
```

The truth of a proposition is evaluated over structure
representing such worlds. One often views a proposition
as specifying a property that one can then test individual
worls for, yielding propositions that are then subject to
ordinary proof construction efforts.


### No Largest Natural Number

As an example in first-order predicate logic, we can
write the expression, *∀n ∃m (m > n + 1)*. In English
we'd pronounce this as "for every *n* there's an *m*
such that *m* is greater than *n*."

To give semantic meaning to such an expression, we
need to specify a semantic domain (the world about
which the expression speaks), along interpretations
that map the syntactic symbols in this expression to
values in the domain. Only then could we evaluate the
expression as being true or not in that domain.

To illustrate, we'll informally describe two different
domains and interpretations for our example expression.

#### One Interpretation

First, we will take the domain to be the universe of
natural number arithmetic. Natural numbers, functions,
and relations will be the entities in the domain. We
will then interpret the names, *n* and *m* as variables
with natural number values, *+* as the natural number
two-argument addition *function*, and *>* as the binary
greater than relation on natural numbers.

Under this interpretation (to this semantic domain), the
expression means the proposition that for any natural
number, *n*, there is some natural number *m*, such that
*m* is greater than one more than *n*. It's easy to see
that the expression can be judged true when evaluated
over this domain structure.

#### A Different Interpretation

On the other hand, the entities of the domain could be
people; *m > n* could be the relation that holds exactly
when *m* is *nicer than n*; *1* could mean a litte bit of
additional *niceness*; and *+* a function that adds up
niceness levels. Under this interpretation, the expression
would assert that in this domain, for every person, *n*,
there is someone person, *m*, who's more than a bit nicer
than they are. Here one can judge the expressions to be
false, as it'd require an infinite supply of ever nicer
people to be true, but the number of people is finite,
so there must be maximally nice people beyond which there
are none who are nicer.

In higher-order predicate logic as typically defined in
Lean, interpretations are more tightly bound to names in
such expressions. We would distingish the two propositions
as their very syntax:

- ∀ (n : Nat), ∃ (m : Nat), (m > n + 1)
- ∀ (n : Person), ∃ (m : Person), (m > n + 1)

In Lean, the meanings of the symbols, *+* and *>* would
then be inferred from context. In the first expression,
Lean would know to take the function, *Nat.add*, as the
meaning of *+*, and the *Nat.lt* relation as the meaning
of *<*.

### Something About People

As an example, domain could have *people* as entities. It could have
a function, *motherOf*, that maps any give person, *p*, to the person
who is the mother of *p*. And there could also be a property of a
person expressed as a predicate, *isBlue*, that takes a person and
indicates whether that person is blue.

With this semantic domain, Ote could then assert the following using
the language of predicate logic: the mother of everyone who's blue
is blue, too. A literal reading would say if p and q are people and
then if p is blue and then if q is the mother of p then q is blue.

- ∀ (p q: Person), isBlue p → isMother q p → isBlue q

In first order logic, it'd be more tedious to express, and there
would be more room for uncaught implicit type errors.

- ∀ p, q, isPerson p → isPerson q → isBlue p → isMother q p → isBlue q


## Differences From Propositional to Predicate Logic

With that introduction, we now highlight key differences
between propositional and predicate logic, focusing on
differences that hold whether one is speaking of simple
first-order predicate logic or the much mroe expressive
higher-order predicate logic provide by the Lean prover.

### Universal and Existential Quantifers

In predicate logic, the set of logical operators is extended
to include existential and universal quantifier expressions.
The universal quantifer expression, *∀x Px* is used to assert
that every object x satisfies the one-argument relation, *P*.
The existential quantifier expressions, *∃x Px* is used to
express the proposition that there is *some* object, *x* that
satisfies the *predicate* P.

In Lean, with its strong typing, these expressions would be
written, *∀ (x : T), P x* and *∃ (x : T), P x*. There are a
few minor differences in syntax. When Lean can infer the type,
*T*, of domain entities, from context, one can omit the explicit
type judgments, *(x : T)* and *(y : T)* and write, *∀ x, P x*
and *∃ x, P x* making the syntax close to that of first-order
predicate logic. In this book we focus heavily on predicate
logic in Lean, viewing first-order logic as a special case.

### Unbounded Diversity of Semantic Domain Structures

Propositional logic has Boolean algebra as its fixed semantic
domain. One evaluates expressions in this language over simple
structures that bind propositional variables to Boolean values.

Predicate logic, by contrast, admits many semantic domains.
You can use it to talk about whatever domain you care to talk
about, provided you can represent it in terms of objects; sets
of objects (in first-order logic with set theory), or types of
objects (in the higher-order logic of Lean); relations among
objects; and functions that take objects as their arguments
and return other objects as results.

As an aside, first-order predicate logic with sets as a theory
extension (*first-order set theory*) speaks in terms of *sets*
of objects. The higher-order predicate logic of Lean speaks in
terms of *types* of objects. For now, you can think of a type
in Lean as defining a set of objects, namely all and only the
objects of that type.

### Typed Higher-Order vs. Untyped First-Order

First-order predicate logic can be considered
as either an untyped, or equivalently (and better)
as a monomorphic (one-type) language. Every entity
has the same type: we'll call it *Object*. In this
sense, first-order logic is like Python. You can
apply any function to any object and it is the job
of the function definition to (1) figure out if it
is really the right kind of object for that function
to process,m and (2) decide what to do if it's not.

Here's a simple version of first-order logic embedded
in Lean 4.

Object is the type of every entity in first-order
logic. Here we use Lean to allow objects of what we
might call different "runtime types" but all having
Object as their "static types". In particular, here
we define (Object.person n) to be the n'th person in
whatever world we might be modeling, and (rock n) to
be the n'th rock.
@@@ -/

inductive Object
| person (n : Nat)
| rock (r : Nat)

/- @@@
In first-order logic, the only way to know what kind
of object on has been given is to apply a predicate.
So here are two predicates, the first true for objects
deemed to be people and the second, rocks.
@@@ -/

def isPerson : Object → Bool
| Object.person _ => true
| _ => false

def isRock : Object → Bool
| Object.rock _ => true
| _ => false

/- @@@
Now we'd like to assert that everyone is mortal.
So we'll define a predicate, which is to say, a
proposition with one or more arguments that, when
applied to arguments, yields a proposition. We'll
think of predicates then as functions that applied
to arguments reduce to propositions. However, as
there are only Object-type entities in first-order
theory, we need a function that takes any Object
value and answers accordingly. This function will
answer *true* if the argument is a person, as all
people are in fact mortal. But if applied to, say,
a rock, the function will still have to answer with
a Boolean value. We define it here to answer false
in such cases, but the reality is the the question
itself doesn't make sense. It's just like in Python
you can pass a string to a function that expects a
number and nothing will go wrong--until you *run*
the program, at which point the argument can be
runtime-tested to determine what kind of thing it
is really meant to represent.
@@@ -/

def isMortal : Object → Bool
| o => if isPerson o then true else false

/- @@@
We're now ready to use our first order logic.
First we define some objects: a person named
*socrates* and a rock that we'll simple call,
*someRock*.
@@@ -/

def socrates : Object := Object.person 0
def someRock : Object := Object.rock 0


/- @@@
Now we can ask whether either of these objects
satisfies the isMortal predicate.
@@@ -/

#eval isMortal socrates   -- yes/true
#eval isMortal someRock   -- no/false

/- @@@
But, again, it doesn't even make sense to
ask if a rock is mortal. If it is then one
might conclude that at some point in time
the rock was alive and it is or eventually
will be dead, and if it's not then what? It
is alive and will live forever? I don't know
about you, but to me, these statements don't
"type check."

Essentially the same world but expressed in
the strongly and statically typed language of
Lean 4.


First, Person and Rock are now separate types,
not just differently shaped terms of the same
type, Object.
@@@ -/

structure Person where
(n : Nat)

structure Rock where
(n : Nat)

/- @@@
Second, we define isMortal' (with a tick mark so
as not to have a name conflict) as a property of
values of type Person only. In more detail, here
we define isMortal' as a predicate parameterized
by a person, with a single constructor for proofs
of propositions obtained by apply8ing the predicate
to a Person. The constructor takes any Person, p, as
an argument and yields a proof of the proposition,
isMortal' p.
@@@ -/

inductive isMortal' : Person → Prop
| everyoneMortal: (p : Person) →  isMortal' p
open isMortal'


/- @@@
Next we define a person entity and a rock entity,
but now they are of completely unrelated types.
@@@ -/

def quine : Person := Person.mk 0
def doorStop : Rock := Rock.mk 0

#check quine    -- type Person
#check someRock -- type Rock

-- We can ask if Quine is mortal
def p0IsMortal : isMortal' quine := everyoneMortal quine

-- But the question whether a rock is mortal is a type error
def r0IsMortal : isMortal' doorStop := sorry

/- @@@
```lean
application type mismatch
  isMortal' doorStop
argument
  doorStop
has type
  Rock : Type
but is expected to have type
  Person : Type
```

Now in first-order logic, one would typically use natural
language to set up a context in which a formal expression
makes sense. One might say this, for example.

We postulate a world inhabited by entities of two kinds,
namely person and rock, with predicates defined to tell
objects of these kinds apart: isPerson and isRock. In this
setting we define the predicate isMortal to take a single
object. If it's a person, the predicate is true of that
object; and if it's a rock, it's false for that object.
In this context, we can express the proposition that all
people are mortal, as follows:
@@@ -/

#check ∀ x, isPerson x → isMortal x

/- @@@
But this predicate is true for rocks, isn't it! You
can see how things can easily go awry when writing
complex specifications in first-order logic. In the
typed logic of Lean we can say it easier and better:
@@@ -/

#check ∀ (p : Person), isMortal' p

/- @@@
No runtime ("reasoning-time") test is needed to tell
if the argument really represents a person or not. The
type checker of Lean 4 does that for us right up front.

#### Older Version of this Subsection

The next major difference between the first-order theory of a
traditional discrete math course, and the predicate logic that
students first learn in this class, is that first-order logic is
*untyped*. It's akin to Python. Everything is just an object in
the first instance. It't only by explicitly testing an object at
runtime that you tell what kind of object you've been handed.

To express the idea that *all people are mortal*, in first-order
thus untyped logic, for example, you'd say, For any object, *p*,
if *p* "is a person" (if *p* satisfies the *isPerson* predicate),
then *p* satisfies the isMortal predicate.
@@@ -/

#check ∀ p, isPerson p → isMortal p

/- @@@
The "∀ p" in effect loops over every object in the universe,
tests each to see if it's a person, and in that case it asserts
that that particular object, *p*, also satisfies the *isMortal*
predicate.

In Lean, by contrast, you would have an inductive type defined,
called Person, and you would say, given any object, p, "of type"
Person, p is mortal. Here it is in Lean.
@@@ -/

#check ∀ (p : Person), isMortal' p

/- @@@
This proposition asserts that if *p* is *any Person*, then *p*
is mortal. There is no possibility that *p* could refer to any
object other than a Person object here, nor than isMoral could
be applied to any object other than a Person. The Lean syntax
and type checkers will not allow it. By constrast there would be
nothing wrong, in first-order predicate logic, with applying the
*isMNortal* predicate to a cheese or some gas, as everything is
in the first instance just an *object*.
@@@ -/

/- @@@
### From Model-Theoretic (Semantic), to Proof-Theoretic, Validity

One of the most notable changes from propositional to predicate logic
is that in the former, one can assess the validity of a proposition by
evaluating it over each of a finite number of interpretations. As soon
as one can interpret a variable in predicate logic as having a natural
number as its meaning, one is into the realm of domains of infinite size.

A new kind a reason will be necessary to replace semantic evaluation.
It will be instead by *deduction* from certain propositions accepted as
*axioms* of the logic, which is to say, accepted valid, without proof.
In fact, propositional logic is incorporated into deductive reasoning
in predicate logic adoption of the propositions in the earlier *axioms*
as the axioms of predicate logic.

Suppose for example that we have two propositions in predicate logic,
P and Q, and we want to show *deductively* that P /\ Q -> Q /\ P. To
do this, we notice the top-level connective is implies. Taking a very
computational perspective, we read the proposition as asserting that if
one assumes that one is given a proof of P /\ Q, then one can derive
from it a proof of Q /\ P. Thus, if P /\ Q is true then so is Q /\ P.

So let's assume we do have a proof of P /\ Q, and let's call it *pq*.
We can apply and_elim_left to *pq* to derive a proof of *p* from it,
and similarly a proof of *q*. We can then apply the proof constructor,
and.intro to these proofs in q-then-p order to have a proof of Q /\ P.

## Propositions as Types: Predicate Logic in Lean 4

Prediate logic is a richer and more expressive language
that propositional logic. Moreover, the higher order logic of
Lean is richer and more expressive than the first-order logic
of the traditional course in discrete mathematics.

In this class we will meet predicate logic through what
we could call a *shallow embedding* of the logic into Lean
We will implement the syntax and rules of deductive reasoning
in predicate logic in Lean as a set of ordinary inductive type
and function definitionss, with no single type expressing the
over syntax or semantics of the logic.
@@@ -/
