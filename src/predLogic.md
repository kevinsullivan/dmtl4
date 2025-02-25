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
how this could work, note that one can encode the natural
numbers as: either the empty set, encoding zero, or as a
set containing the set representing a one-smaller number.
The nesting level represents the value, just as for *Nat*
in Lean.

The larger point here is that the choice of any given
logic in which to reason about the world brings with it
a form of structure in terms of which one can represent
specific states of the real world, over which expressions
are evaluated.

## Semantic Domains for Predicate Logic

In particular, predicate logic brings along with it a much
richer form of structure (than vector of Boolean) that one
use to represent real world conditions of interest. A set
of possible world situations no longer has to be encoded
just as a vector of binary Boolean values. We can represent
a world now in essentially *relational* terms. Predicate
logic is the core theory underpinning relational databases.
Our world state representation structures can now have:

- *objects* representing corresponding objects in the real domain (e.g., "Tom", "Mary")
- *functions* from objects to objects  in the real world (e.g., motherOf Tom = Mary)
- *relations* among objects in the real world (e.g., youngerThan Tom Mary)
- *sets of objects* (e.g., { "Tom", "Mary" }) [unary relation]

To know how to use predicate logic effectively, it really
helps to think about how you want to represent the space of
all of the possible worlds about which you might speak, and
how to represent specific individual worlds in that space.
Think in relational terms.
@@@ -/

/- @@@
The syntax of predicate logic is then set up to provide
nice ways to talk about such world representations. The
syntax provides *constant* symbols (referring to fixed
domain objects); (free) *variables*, also interpreted as
referring to objects; *function* symbols (and arguments,
interpreted as referring to functions in the world); and
*predicate* symbols refering to relations in the domain. 
Predicate logic inherits the connectives of propositional 
logic, adds two kinds of quantified expressions, and puts
it all together into a syntax of *well formed formula* in
predicate logic.

## Limited Expressiveness of First-Order Predicate Logic

The variant of predicate logic taught in typical DMT1 courses
is called first-order predicate logic. The logic of Lean is a
higher-order logic. The difference is in the generality of what
can be expressed in each of these logic.

To see the difference concretely, let's consider what properties
a *friendOf* relation should have on some new social network. It
could be *symmetric*, as it is on *FB*; or one might prefer for
it not necessarily to be symmetric. Maybe a *follows* relation
would be better. I follow Bill Gates but he doesn't follow me.

In first-order logic we can use the *universal quantifer* syntax
to specify that our *friendOf* relation is (to be) symmetric. We can
write this as *∀x∀y(friendOf(x,y)↔friendOf(y,x)).* The variables,
*x* and *y*, are *bound* by the quantifer to range over all objects
in the semantic domain. The predicate after the comma then checks
whether all such pairs of objects satisfy the following predicate.

A major restriction on expressiveness imposed by first-order logic
is that quantified variables can be range only over objects. One
cannot quantify over all sets of objects, functions, or relations.
In first order theory we can express the idea that some particular
relation is symmetric.

```lean

```

What we can't express in first-order logic
is the concept of symmetry as a generalized property that *any* given
binary relation on *any* set of objects of *any* kind might or might
not have. And yet being able to reason fluently with concepts at this
level of generality is essential for any literate mathematician.  in terms of We cannot express the *property* of a relation
of *being symmetric,* a crucial degree of mathematical generality*,
in first order theory because we cannot talk about *all relations*.

## The Enhanced Expressiveness of Higher-Order Logic in Lean

The most crucial property of Lean for this course, and for research
worldwide on the formalization of advanced mathematics, is that Lean
implements a higher-order logic in which you can express concepts of
great generality by quantifying not only over elementary values but
over such things as types, functions, propositions and predicates,
and so forth.  

As an one example, in higher order predicate logic
in Lean, one can define *generalized* properties of relations: for
example the property of a binary relation r on a set s of values of
some type T that r relates any two values in one direction only if
it it also relates them in the other order. 

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
