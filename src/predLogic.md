# Predicate Logic

<!-- toc -->

In propositional logic, syntactic variable expressions
are interpreted only over sets of Boolean state values.

- PressureTooHigh /\ ORingsFailing
- (GreenLight \\/ RedLight) /\ ~(GreenLight /\ RedLight)

## Limited Expressiveness of Propositional Logic

Within the logic one can thus only speak about real world
situations in terms of sets of Boolean variables and their
values. The choice of propositional logic as a reasoning
language limits one to representing real-world conditions
in these very spartan, sometimes inadequate, and sometimes
misleading terms.

As an example, suppose you want to reason about the safety
of a driving vehicle. It has a brake and a steering system.
Each is deemed 70.5% likely to be operational. That's high
(by some low standards), so suppose we model this world in
Boolean terms as { BrakeOk := true, SteeringOk := true }.

Now of course we want both brakes and steering for safety,
so we evaluate BrakesOk /\ SteeringOk over this structure
(intepretation) and get *true*. We might make the mistake
of believing that the result soundly reflects reality. If
the threshold for being Ok is a greater than 50% chance of
success, this condition still doesn't hold: assuming that
the failures are independent, we find that the combination
of the probabilities yields a likelyhood of the overall
*system* being ok is less than 50%.

## Enhanced Expressiveness of Predicate Logic

A way out of this bind is to pick a more expressive
logic: one that enables us to represent worlds in richer
terms so that we might be enabled to reason about real
worlds more effectively. The varieties of predicate logic
provide such improved expressiveness.

In a predicate logic, we can speak not only in terms of
Boolean variables and values, and the usual operations on
them, but also in terms of *sets* of objects, *relations*
between objects, properties (via predicates) of objects, 
*functions* that take objects as arguments and return them
as results, and about whether all, or respectively at least
one, of the elements of a given set has a given property.

It's on the foundation of a simple predicate logic that
most of contemporary mathematics rests. To give a sense
how this could one, note that one can encode the natural
numbers as either the empty set representing zero, or as a
set containing the set representing a one-smaller number.

The most salient point here, though, is that the choice
of predicate logic as a formal *language* comes with this
much richer range of formal representations of real world
situations. A set of possible world situations no longer
has to be represented only using Boolean variables, but
is now represented by *objects*, *functions* from tuples
of objects to other objects, *sets* of objects with given
properties, and *relations* that associate objects that,
together, have certain properties, such as one particular
number being *less than* another.

To start to write practical predicate logic expressions,
one must have specified such a formal semantic domain, i.e.,
a form of world state representations over which expressions
in predicate logic will be written and evaluated. The syntax
of predicate logic then provides for *constant* symbols,
interpreted as referring to domain objects; *variables*,
also (when *free*, not *bound* by a quantifier, discussed
later) to be interpreted as referring to objects; *function*
names, interpreted as referring to functions in the semantic
domain; and set/relation symbols used to refer to sets and
relations in the semantic domain. An expression in predicate
logic is then evaluted by mapping these syntactic elements
to their semantic meanings and checking if the resultis true
in the semantic domain.

Without elaborating, we will note that what we've described
here is a *formal* semantics. The particular representation
of the real world, the form of structure over which predicate
logic expressions can be evaluated, will have its own intended
meanings in the real world. To have a complete understanding
of the soundness of formal reasoning over formal structures,
one must also consider the real semantics of the structures.

## First-Order Predicate Logic

The variant of predicate logic taught in typical DMT1 courses
is called first-order predicate logic. The logic of Lean is a
higher-order logic. The difference is in the generality of what
can be expressed in each of these logic.

To see the difference concretely, let's consider what properties
a *friendOf* relation should have on some new social network? It
could be *symmetric*, as it is on *FB*; or one might prefer for
it not necessarily symmetric. I *follow* Bill Gates on a site
but on that site he doesn't follow me.

In first-order logic we can use the *universal quantifer* syntax
to specify that our *friendOf* relation will be symmetric. We can
write this as *∀ p1 p2, friendOf p1 p2 ↔ friendOf p2 p1.* Here, the
variables, *p1* and *p2*, are *bound* by the quantifer to range over
all objects in the semantic domain. The predicate after the comma
then asserting that for any such pair, if the first is a *friendOf*
the second, then the second is necessarily a *friendOf* the first.

A major restriction on expressiveness imposed by first-order logic
is that quantified variables can be range only over objects and not
over such things as sets of objects, functions, or relations. In first
order theory we can express the notion that that some *particular*
relation is symmetric; and to say that we had to generalize over all
pairs of objects in the domain. But what we can't say in first-order
logic is that *any* relation, *r*, is symmetric if for every pair of
objects, *p1* and *p2*, if *r* relates *p1* to *p2*, then *r* also
relates *p2* to *p1*. We cannot express the *property* of a relation
of *being symmetric,* a crucial degree of mathematical generality*,
in first order theory because we cannot talk about *all relations*.

## Higher-Order Predicate Logic

The most crucial property of Lean for this course, and for research
worldwide on the formalization of advanced mathematics, is that Lean
implements a higher-order logic in which you can quantify over such
things: not only objects of given types, but over types themselves,
along with sets, functions, propositions, predicates, and so forth.

As an one example, in Lean one can define the *generalized property,* of a binary relation on objects of any type, of being *symmetric* like this:

```lean
def symmetric := 
∀ (T : Type) 
  (R : T → T → Prop) 
  (t1 t2 : T),
r t1 t2 ↔ r t2 t1
```

That is, for any type of objects, *T* (quantification over types), and for any binary relation, *R,* on values of this type (quantification over relations), what it means for *R* to be symmetric is that for any two objects, *t1, t2*
of type *T* (a first-order quantification), if *R* relates *t1* to *t2* then it also relates *t2* to *t1*.

We can then *apply* such generalized definition to any particular binary relation on any type of values (let's say, *isFriend*, on values of type, *Person*) to derive the proposition that *that* relation is symmetric. The expression, *symmetric Person isFriend*, would then reduce to the first-order proposition, *∀ t1 t2 : Person, *isFriend t1 t2 <->  isFriend t2 t1*. 

For the working mathematician it's crucial to be able to reason and speak in terms of such abstract and generalized properties of complex things. We speak of relations being symmetric, reflexive, transitive, well founded, and so on, without having to think about specific relations. We think of operation being commutative, associative, invertible, again in precise but abstract and general terms, independent of particular operations. In the first-order logic of the usual CS2: DMT1 class, that's just not possible. In Lean 4, it is completely natural and incredibly useful.

The result has been an explosion in the community of mathematicians using Lean 4 to formalize and verify theorems in many branches of advanced mathematics. That in turn has sparked deep interest in computer science in the use of Lean 4 for research and development in trustworthy computing, among many other areas. The rest of this chapter skips over first-order logic to introduce predicate logic through its higher-order, much more useful and relevant variant, in Lean.
