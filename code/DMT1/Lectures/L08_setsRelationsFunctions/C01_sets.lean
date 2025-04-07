import Mathlib.Data.Set.Basic
namespace DMT1.Lectures.setsRelationsFunctions.sets

/- @@@
# Theory of Sets

<!-- toc -->


A set is intuitively understood as a *collection* of objects.
Such a collection can be finite or infinite. Infinite sets can
vary in the degrees of their infinite sizes. For example, the
set of natural numbers less than five is finite, the set of all
natural numbers is *countably* infinite, and the set of *real*
numbers is said to be *uncountably infinite*.

Like Boolean algebra or arithmetic, set theory is algebraic in
that it has both objects (sets) and operations involving them.
Your aim in this chapter is to understand the following:

- (1) the *language* of sets, their properties, and operations
- (2) how sets can be represented as *one-argument* predicates
- (3) understand the logical specifications of set operations
- (3) understand how to prove propositions about sets

The first section of this chapter introduces sets and how they
can be specified, and are represented in constructive logic, by
logical predicates. The second section specifies set operations
as in entirely logical terms. The good news is that the notions
of sets, properties of sets, and set operations all reduce to
logical operations, which you already understand!

## Sets

In what's sometimes called naive set theory, one thinks of a
set as a collection of objects. Some objects are "in" the set.
In type theory, we consider only sets of objects of one specific
type. So we can talk about a set of natural numbers or a set of
people, but we won't have sets that contain numbers and people.

Two examples of sets of natural numbers would be the set of all
even numbers, and the set of all natural numbers less than five.
An example of a set of people would be the set of those people
who are taking this class for credit this semester.

In each of these examples, we define a set by first saying what
*type* of objects it contains, and then by stating the specific
property of any such value that determines whether it's in the
set or not. For example, rather than *the set of even numbers*
we can say *the set of natural numbers, n, such that n is even*.
Everything before the second comma introduces the type of object
in the set (natural numbers) and give a name to some arbitrary
value of that type. The rest, *such that n is even*, defines
the property of any given *n* that determines whether it is to
be considered in, or not in, the set. Here the condition is that
*n* is even.

### Specification and Representation

In Lean, a set, a, is represented by a membership *predicate:*
one that takes a single argument, let's call it *a*, of some type,
*α*, and that reduces to a proposition about that a (such that a
is even), where such a value, *a*, is defined to be in the set
if it satisfies the predicate--that is, if there's a proof of the
proposition, *(s a)*m; otherwise a is defined not to be in the set.

For example, we've seen several definitions of *evenness* as a
predicate on natural numbers. A small turn of the imagination
lets us now talk about the set of even numbers, call it evNum,
as comprising all of those numbers, n, for which there is a
proof of (evNum n). The predicate defines the set in question.
And in Lean we represent a Set as its *membership* predicate.

It's important to note that we are now operating entirely in
the realm of logical specifications, not implementations. Sets in
Java are data structures that contain the values considered to be
in a set. Sets are definitely *not* represented as data structures
in Lean. Among other things we'd not be able to represent sets,
such as the natural numbers, with infinite numbers of elements.
Rather sets are defined by logical specifications, in Lean in
the form of predicates, define in just the right way so that all
the elements you want in a set satisfy the predicate and no other
values do.

You can see the actual definition of *Set* in Lean by going to
its definition. Right click on Set and select *go to definition*.
@@@ -/

#reduce Set
-- fun α => α → Prop
-- a polymorphic type

-- specializations
#reduce Set Nat
#reduce Set Bool
#reduce Set Prop


/- @@@
In this class we distinguish two uses of the same predicate
when defining a set in Lean. First, a one-place predicate can
be understoood to *specify* a set: the set of all and only the
objects that can be proven to satisfy it.
@@@ -/


/- @@@
Exercises:

- What predicate would specify the set of all natural numbers?
- What predicate would specify the empty set of natural numbers?
- Define a predicate that would specify the set of even numbers.
@@@ -/


/- @@@
Second, Lean also uses a predicate to *represent* any given set, but
this fact should be understood as an inessential design decision that
is *abstracted away* by the Set *API* in Lean.
@@@ -/

#check Set
-- def Set (α : Type u) := α → Prop

/- @@@
Quoting from mathlib: A set is a collection of elements of some
type `α`. Although `Set` is defined as `α → Prop`, this is an
implementation detail which should not be relied on. Instead,
`setOf` and membership of a set (`∈`) should be used to convert
between sets and predicates.
@@@ -/

/- @@@
Example: Can't directly treat Prop as Set
@@@ -/
def aNatProp : Nat → Prop := λ n => True
-- #check 1 ∈ aNatProp       -- won't work

def s : Set Nat := setOf aNatProp   -- can coerce prop to set
#check 1 ∈ s              -- gain set language and notations
#check (s 1)              -- this "works" but is unpreferred
def t : Nat → Prop := s   -- can treat set as prop

/- @@@
Good to know Lean details.

- Define a set, s, by applying setOf to a predicate: α → Prop
- Beyond α → Prop, being a set brings operations and notations
- Check membership of object a in set s using a ∈ s, not (s a)
@@@ -/

/- @@@
The real advantage, in Lean, of representing sets as predicates
is that it confers the ability to strip set theory abstractions to
their underlying logical representations, at which point one can
then use all the machinery of predicate logic, now well understood,
to reason about propositions *in set theory*. If one likes to think
in proof strategy terms, this one could be called proof "by the
definition of," though proof "by the underlying representation of"
is probably a better term.
@@@ -/

/- @@@
### Set Notations

In the language of set theory, there are two especially
common notations for represeting sets. They are *display*
and (set) *comprehension* notation.

#### Display Notation

To represent a finite set of objects in mathematical writing,
you can give a comma-separated list of members between curly
braces. The set of small numbers (0 to 4) can be represented
in this way as *{ 0, 1, 2, 3, 4 }*. Sometimes we will want to
give a set a name, as in, *let s = { 0, 1, 2, 3, 4 }*, or
*let s be the set, { 0, 1, 2, 3, 4 }.*

Lean supports display notation as a set theory notation.
One is still just definining a membership predicate, but
it looks like the math you'll see in innumerable books and
articles. Moreover, when you look at such notations from
now on, even if you've seen them before, you can think
about how they can be seen as expressions of membership
predicates.


The corresponding predicate in this case, computed by Lean,
is *fun b => b = 0 ∨ b ∈ {1, 2, 3, 4}*. In the following
example, Lean doesn't infer that the set type is Set Nat,
so we have to tell it so explicitly.
@@@ -/

def       s1 : Set Nat := { 0, 1, 2, 3, 4 } -- repped as ...
#reduce   s1   -- fun b => b = 0 ∨ b ∈ {1, 2, 3, 4}

/- @@@
#### Comprehension Notation

Sets can also be specified using what is called *set
comprehension* notation. Here's an example using it to
specify the same small set.
@@@ -/

def s2 : Set Nat := { n : Nat | n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 }

-- The empty set (of natural numbers)
def noNat' : Set Nat := { n : Nat | False}
def noNat : Set Nat := ∅                    -- set theory notation!

--
def allNat' : Set Nat := { n : Nat | True}
def allNat : Set Nat := Set.univ            -- Univeral set (of all Nats)

-- Uncomment the next line to see the error
-- example : 3 ∈ noNat := (_ : False)      -- unprovable, stuck
example : 3 ∉ noNat := fun h => nomatch h   -- proof by negation

/- @@@
We pronounce the expression (to the right of the := of course) as
*the set of values, n, of type Nat, such that n = 0 ∨ n = 1 ∨ n = 2 ∨
n = 3 ∨ n = 4. The curly braces indicate that we're defining a set. The
*n : Nat* specifies the set of set members. The vertical bar is read
*such that*, or *satisfying the constraint that*. And the membership
predicate is then written out.

You can check that this set, s2, has the same membership predicate as s1.
@@@ -/

#reduce s2

/- @@@
Example: Assume there's a type of objects call Ball and a predicate,
Striped, on balls. Use set comprehension notation to specify the set of
striped balls. Answer: { b : Ball | Striped b }. Read this expression
in English as *the set of all balls, b, such that b is striped*, or
more concisely and naturally simply as *the set of all striped balls*.
@@@ -/

axiom Ball : Type
axiom Striped : Ball → Prop
def sb : Set Ball := { b : Ball | Striped b}

-- Question: Can we define sets of sets? Yes! Example
def ssb : Set (Set Ball) := { sb } -- a set of sets


/- @@@
### Homogenous vs Heterogeneous Sets

The preceding example involved a set of natural numbers.
In Lean, such a set, being defined by a predicate on the
natural numbers, cannot contain elements that are not of
the natural number type. Sets in Lean are thus said to be
*homogeneous*. All elements are of the same type. This
makes sense, as sets are represented in Lean by predicates
that take arguments of fixed types.

A *heterogeneous* set, by contrast, can have members of
different types. Python supports heterogeneous sets. You
can have a set containing a number, a string, and a person.
The track in Python is that all objects actually have the
same *static* type, which is *Object*. In the end, even in
Python, sets are homogeneous in this sense.

In Lean, and in ordinary mathematics as well, sets are most
often assumed to be homogenous. In mathematical communication,
one will often hear such phrases as, *Let T denote the set of
natural numbers less than 5.* Notice that the element type is
made clear.

In support of all of this, Set, in Lean, is a type builder
polymorphic in the element type. The type of a set of natural
numbers is *Set Nat*, for example, while the type of a set of
strings is *Set String*.

The following example shows that, in Lean, the even and small
predicates we've already defined can be assigned to variables
of type *Set Nat*. It type-checks! Sets truly are specified by
and equated with their membership predicates in Lean.
@@@ -/

def ev := λ n : Nat => n % 2 = 0
def small := λ n : Nat => n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4


def ev_set' : Set Nat := ev         -- ev is a predicate
def small_set' : Set Nat := small   -- small is too

/- @@@
In mathematics, per se, sets are not equated with logical
predices. Rather, to represent sets (to *implement* them,
as it were) as predicates in Lean is just a very nice and
convenient way to go. So, really, there are two things on
your plate in this chapter: (1) understand the language of
set theory and how set operations are defined logically, and
(2) understand how representing sets as membership would be to use either display or
set comprehension notation. Here are stylistically improved
definitions of our sets of even and small natural numbers.
We will use these definitions in running examples in the
rest of this chapter.
@@@ -/

def ev_set : Set Nat := { n : Nat | ev n }
def small_set : Set Nat := { n | small n }

#reduce (types := true) small_set 4

example : 4 ∈ small_set :=
  -- 4 = 0 ∨ 4 = 1 ∨ 4 = 2 ∨ 4 = 3 ∨ 4 = 4
Or.inr
(
  (Or.inr
    (
      Or.inr
      (
        Or.inr
          (
            rfl
          )
      )
    )
  )
)

example : ∃ (n : Nat), n ∈ small_set :=
Exists.intro 0 (Or.inl rfl)


/- @@@
The take-away is that, no matter one's choice of notation,
sets are truly represented in Lean by *logical* predicates.
The great news is that you already understand the logic so
learning set theory is largely reduced to learning the set
algebraic concepts (the objects and operations of set theory)
and in particular how each concept reduces to underlying logic.
@@@ -/

/- @@@
### Universal and Empty Sets

With membership notation under our belts, we can now better
present the concepts and notations of the universal and the
empty set of elements of a given type.

#### Universal set

The universal set of a values of a given type is the set
of *all* values of that type. The membership predicate for
the *universal* set is thus true for every element of the
set. *True* is the (degenerate, parameterless) predicate
that satisfies this condition. It is true for any value,
so every value is in a set with True as its membership
predicate.

To be precise, the membership predicate for the universal
set of objects of any type *T*, is *λ (a : T) => True.*
When it is applied to any value, *t*, of type T, the result
is just the proposition, *True*, for which we always have
the proof, *True.intro*.

In Lean, the universal set of objects of a given type is
written as *univ*. The definition of *univ* is in Lean's
*Set* namespace, so you can use *univ* either by first
opening the *Set* namespace, or by writing *Set.univ*.
@@@ -/

open Set

#reduce univ        -- fun _a => True
#reduce univ 0      --           True
#reduce univ 123456 --           True

/- @@@
#### Empty set

The empty set of values of a given type, usually
denoted as ∅, is the set
containing *no* values of that (or any) type. It's
membership predicate is thus false for every value of
the type. No value is a member. Formally, the membership
predicate for an empty set of values of type T is
*λ (t : T) => False*.

Again we emphasize that set theory in Lean is built on and
corresponds directly with the logic you've been learning all
along. We've now seen that (1) sets are specified by membership
predicates; (2) the universal set is specified by the predicate
that is true for any value; (3) the empty set is specified by
the predicate that is false for any value; (4) the ∈ operation
builds the proposition that a given value satisfies the membership
predicate of a given set; (5) proving propositions in set theory
reduces to proving corresponding underlying logical propositions.
@@@ -/

/- @@@
At an abstract level, Set theory, like arithmetic, is a mathematical
system involving objects and operations on these objects. In arithmetic,
the objects are numbers and the operations are addition, multiplication,
etc.  In Boolean algebra, the objects are true and false and operations
include *and, or,* and *not*. In set theory, the objects are sets and
the operations include set membership (∈), intersection (∩), union (∪),
difference (\), complement (ᶜ) and more. We now turn to operations on
sets beyond mere membership.
@@@ -/

/- @@@
## Operations on Sets

Specifying sets, from set theory, as predicates in propositional
logic, paves the way to:

- (1) specifying *operations* on sets as definitions in predicate logic,
- (2) proving propositions in set theory by proving the propositions to which they desugar.

To acquire the skill of proving propositions in set theory you
*must* learn how each operation is formally defined in predicate logic,
and then be able to prove the corresponding the *logical* propositions.

To that end, here's a table that summarizes the correspondence
between operations in set theory, on one hand, and their specifications
in the language of predicate logic (as implemented in Lean), on the other.


| Name          | Notation  | Specification               | Logical Specification          |
|---------------|-----------|-----------------------------|--------------------------------|
| Set           | set α     | axioms of set theory        | (α → Prop)                     |
| membership    | x ∈ a     | a satisfies predicate       | (a x)                          |
| intersection  | s ∩ t     | { a \| a ∈ s ∧ a ∈ t }      | fun a => (s a) ∧ (t a)         |
| union         | s ∪ t     | { a \| a ∈ s ∨ a ∈ t }      | fun a => (s a) ∨ (t a)         |
| complement    | sᶜ        | { a \| a ∉ s }              | fun a => ¬(s a)                |
| difference    | s \ t     | { a \| a ∈ s ∧ a ∉ t }      | fun a => (s a) ∧ ¬(t a) )      |
| subset        | s ⊆ t     | ∀ a, a ∈ s → a ∈ t          | fun a => (s a) → (t a)         |
| proper subset | s ⊊ t     | s ⊆ t ∧ ∃ w, w ∈ t ∧ w ∉ s  | ... ∧ ∃ w, (t w) ∧ ¬(s w)      |
| product set   | s × t     | { (a,b) | a ∈ s ∧ b ∈ t }   | fun (a, b) => (s a) /\ (t b)   |
| powerset      | 𝒫 s       | { t | t ⊆ s }               | fun t => ∀ ⦃a : ℕ⦄, t a → s a  |
@@@ -/

#reduce Set
#reduce Set.Mem
#reduce Set.inter
#reduce Set.union
#reduce Set.compl
#reduce Set.diff
#reduce @Set.Subset
#reduce Set.prod
#reduce Set.powerset

/- @@@
Exercise: What precisely are the elements of the powerset of the
product set of two finite sets, S and T?

Exercise: How many elements are in the powerset of the product
set of two finite sets, S and T, of sizes s and t, respectively?
@@@ -/

/- @@@
Let's elaborate on each of these concepts now.

### Membership Predicates

Let's start by building on our understanding of predicates.
Here are two *predicates* on natural numbers. The first is true
of even numbers. The second is true of any number that is small,
where that is defined as the number *being equal to 0, *or* being
equal to 1 *or*, ..., *or* being equal to 4.* The first predicate
can be understood as specifying the set of even numbers; the second
predicate, a set of small numbers.
@@@ -/

/- @@@
Self test: What *proposition* is specified by the expression,
*small 1*? You should be able to answer this question without
seeing the following answer.

Answer: Plug in a *1* for each *n* in the definition of *small*
to get the answer. There are 5 places where the substitution has
to be made. Lean can tell you the answer. Study it until you see
that this predicate is true of all and only the numbers from 0 to
4 (inclusive).
@@@ -/

#reduce (types := true) (small 1)

/- @@@
The result is *1 = 0 ∨ 1 = 1 ∨ 1 = 2 ∨ 1 = 3 ∨ 1 = 4*. This
proposition is true, of course, because *1 = 1*. So *1* is proved
to be a member of the set that the predicate specifies. Similarly
applying the predicate to 3 or 4 will yield true propositions; but
that doesn't work for 5, so 5 is not in the set that this predicate
specifies.
@@@ -/

/- @@@
To formally prove that 1 is in the set, you prove the underlying
logical proposition, *1 = 0 ∨ 1 = 1 ∨ 1 = 2 ∨ 1 = 3 ∨ 1 = 4*. A
proof of *set* membership thus reduces to a proof of an ordinary
logical proposition, in this case a disjunction. Again an insight
to be taken from this chapter is that set theory in Lean reduces
to correspondinglogic you already understand and know how to deal
with.

As a reminder, let's prove *1 = 0 ∨ 1 = 1 ∨ 1 = 2 ∨ 1 = 3 ∨ 1 = 4*.

First, recall that ∨ is is right associative, so what we need to
prove is *(1 = 0) ∨ (1 = 1 ∨ 1 = 2 ∨ 1 = 3 ∨ 1 = 4)*. It takes
just a little analysis to see that there is no proof of the left
side, *1 = 0*, but there *is* a proof of the right side. The right
side is true because 1 = 1. Our proof is thus by *or introduction*
on the right applied to a proof of the *right* side, which we can
now slightly rewrite as (1 = 1) ∨ (1 = 2 ∨ 1 = 3 ∨ 1 = 4).

Be sure to see that using right introduction discards the left side
of the original proposition and requires only a proof of the right.
A proof of it, in turn, is by or introduction on the left applied to
a proof of 1 = 1. That proof is by the reflexive property of equality
(it's always true that anything equals itself). This idea is expressed
in Lean using *rfl*.

Exercise: Give a formal proof that 1 satisfies the *small*
predicate. We advise you to use top-down, type-guided structured
proof development to complete this simple proof. We give you the
or introduction on the right to start.
@@@ -/

example : small 1 := (Or.inr (Or.inl rfl))
example : small 3 := Or.inr (Or.inr (Or.inr (Or.inl (Eq.refl 3))))

/- @@@
### Membership Again

TODO: Combine with preceding section

We've already seen that we can think of a predicate as defining
a set, and that a value is a member of a set if and only if it
satisfies the membership predicate.

That said, set theory comes with its own abstractions and notations.
For example, we usually think of a set as a *collection* of objects,
even when the set is specified by a logical membership *predicate*.
Similarly set theory gives us notation for special sets and all of
the operations of set theory.

As an example, the proposition that 1 is a member of small_set
would be written as *small_set 1* if we're thinking logically;
but in set theory we'd write this as *1 ∈ small_set*. We would
pronounce this proposition as *1 is a member of small_set*.

From now on you should try to interpret such an expression in
two ways. At the abstract level of set theory, it asserts that
1 is a member of the collection of elements making up small_set.
At a concrete, logical, level, it means that *small_set 1*, the
logical proposition that 1 satisfies the small_set predicate, is
true, and that you can construct a proof of that.

The very same proof proves 1 ∈ small_set. All these notations mean
the same thing, but set theory notation encourages us to think more
abstractly: in terms of sets (collections), not predicates, per se.

Nevertheless, to construct proofs in set theory in Lean, you
must understand how the objects and operations in set theory
are defined in terms of, and reduce, to propositions in pure
logic. What you will have to prove are the underlying logical
propositions.

Here, for example, we *state* a proposition using set theory
notation, but the proof is of the underlying *or* proposition.
@@@ -/

#check 1 ∈ small_set      -- membership proposition in set theory
#reduce 1 ∈ small_set     -- this proposition in predicate logic
example : 1 ∈ small_set := Or.inr (Or.inl rfl)  -- a proof of it

/- @@@
The lesson is that when you look at an expression in set theory
you really must understand its underlying logical meaning, for
it's the underlying logical proposition that you'll need to prove.

So we're now in a position to see the formal definition of the
membership operation on sets in Lean. In the Lean libraries, it
is *def Mem (a : α) (s : Set α) : Prop := s a*, where α is a type.
The notation ∈ reduces to corresponding logic. More conretely, the
set theory proposition a ∈ s reduces to applying the set, s, viewed
as a membership predicate, to the argument, a (thus the expression,
*s a*) to yield a proposition, (s a), that is true if and only if
a is in s.
@@@ -/

/- @@@
Exercises.

(1) We expect that by now you can construct a proof
of a disjunction with several disjunctions. But practice is still
great and necessary. Try erasing the given answer and re-creating
it on your own. By *erase* we mean to replace the answer with
*_*. Then use top-down, type-guided refinement to derive a complete
proof in place of the *_*.
@@@ -/

#reduce 3 ∈ small_set
example : 3 ∈ small_set := Or.inr (Or.inr (Or.inr (Or.inl rfl)))

/- @@@
A take-away is that the set theory expression, x ∈ X,
simply means, that x satisfies the membership predicate
that defines the set X. To prove x ∈ X, substitute x for
the formal parameter in the membership predicate (apply
the predicate to x) and prove the resulting proposition.
@@@ -/

/- @@@
### Intersection

Given a type, T, and two sets, s1 and s2 of T-valued elements
(members), the *intersection* of s1 and s2 is the set the members
of which are those values that are in both s1 *and* s2. The intersection
of s1 and s2 is written mathematically as *s1 ∩ s2*.

The intersection operation is defined in Lean as *inter (s₁ s₂ : Set α) :
Set α := {a | a ∈ s₁ ∧ a ∈ s₂}*. Given two sets of alpha values, the result
is the set of values, a, that satisfy both conditions: a ∈ s₁ ∧ a ∈ s₂. Set
intersection (∩) is defined by predicate conjunction (∧).

Intersection of sets corresponds to logical conjunction (using *and*)
of the respective set membership predicates. The similarity in notations
reflects this fact, with ∩ in the language of set theory reducing to ∧ in
the language of predicate logic. The following Lean codeillustrate the point.
@@@ -/

#reduce Set.inter
-- fun s₁ s₂ a => s₁ a ∧ s₂ a



variable (α : Type) (s t : Set α)
#check s ∩ t    -- the intersection of sets is a set
#reduce s ∩ t   -- its membership predicate is formed using ∧


/- @@@
As another example, the intersection of our even (ev) and small sets,
corresponding to the conjunction of their membership predicates,
contains only the elements 0, 2, and 4, as these are the only values
that satisfy both the ev *and* small predicates.
@@@ -/

def even_and_small_set := ev_set ∩ small_set  -- intersection!
#reduce (0 ∈ even_and_small_set)  -- membership proposition

/- @@@
As an example, let's prove 6 ∈ even_and_small_set. We'll first look
at the logical proposition corresponding to the proposition in set
theory assertion, then we'll try to prove tha underlying *logical*
proposition.
@@@ -/

#reduce 6 ∈ even_and_small_set

-- to prove: 0 = 0 ∧ (6 = 0 ∨ 6 = 1 ∨ 6 = 2 ∨ 6 = 3 ∨ 6 = 4)
example: 6 ∈ even_and_small_set := sorry

/- @@@
The proposition to be proved is a conjunction. A proof of it
will have to use And.intro applied to proofs of the left and
right conjuncts. The notation for this is ⟨ _, _ ⟩, where the
holes are filled in with the respective proofs. We can make a
first step a top-down, type-guided proof by just applying this
proof constructor, leaving the proofs to be filled in later.
The Lean type system will tell us exactly what propositions
then remain to be proved.
@@@ -/

example: 6 ∈ even_and_small_set := ⟨ sorry, sorry ⟩

/- @@@
On the left, we need a proof of *6 ∈ ev_set*. This can also
be written as *ev_set 6*, treating the set as a predicate.
This expression then reduces to 6 % 2 = 0, and further to
*0 = 0*. That's what we need a proof of on the left, and
*rfl* will construct it for us.
@@@ -/

example: 6 ∈ even_and_small_set := ⟨ rfl, sorry ⟩

/- @@@
Finally, on the right we need a proof of 6 ∈ small_set.
But ah ha! That's not true. We can't construct a proof
of it, and so we're stuck, with no way to finish our
proof. Why? The proposition is false!

Exercise: Prove that 6 ∉ small_set. Here you have to
recall that 6 ∉ small_set means ¬(6 ∈ small_set), and
that in turn means that a proof (6 ∈ small_set) leads
to a contradiction and so cannot exist. That is, that
6 ∈ small_set → False.

This is again a proof by negation. We'll assume that
we have a proof of the hypothesis of the implication
(h : 6 ∈ even_and_small_set), and from that we will
derive a proof of False (by case analysis on a proof
of an impossibility using nomatch) and we'll be done.
@@@ -/

example : 6 ∉ even_and_small_set :=
  fun (h : 6 ∈ even_and_small_set) => nomatch h

#check Set


/- @@@
### Union

Given two sets, s and t, the union of the sets, denoted as
s ∪ t, is understood as the collection of values that are
in s *or* in t. The membership predicate of s ∪ t is thus
*union (s₁ s₂ : Set α) : Set α := {a | a ∈ s₁ ∨ a ∈ s₂}.
As an example, we now define even_or_small_set as the union
of the even_set and small_set.
@@@ -/

#reduce @Set.union
-- fun {α} s₁ s₂ a => s₁ a ∨ s₂ a



def even_or_small_set := ev_set ∪ small_set

/- @@@
Now suppose we want to prove that 3 ∈ even_or_small_set. What
we have to do is prove the underlying logical proposition. We
can confirm what logical proposition we need to prove using reduce.
@@@ -/

#reduce 3 ∈ even_or_small_set

/- @@@
Exercises. Give proofs as indicated. Remember to analyze the
set theoretic notations to determine the logical form of the
underlying membership proposition that you have to prove is
satisfied by a given value.
@@@ -/

example : 3 ∈ even_or_small_set := Or.inr sorry
example : 6 ∈ even_or_small_set := sorry
example : 7 ∉ ev_set ∪ small_set := sorry
-- uncomment the following line to see error
-- example : 7 ∈ ev_set := _   -- stuck
example : 7 ∉ ev_set := λ h => sorry

/- @@@
### Complement
Given a set s of elements of type α, the complement of s,
denoted sᶜ, is the set of all elements of type α that are
*not* in s. Thus *compl (s : Set α) : Set α := {a | a ∉ s}.*

So whereas intersection reduces to the conjunction of membership
predicates, and union reduces to the disjunction of membership
predicates, the complement operation reduces to the negation of
membership predicates.
@@@ -/

#reduce sᶜ    -- fun x => x ∈ s → False means fun x => x ∉ s
-- fun x => x ∈ s → False

variable (s : Set Nat)
#check sᶜ     -- Standard notation for complement of set s


/- @@@
Exercises:

(1) State and prove the proposition that 5 ∈ smallᶜ. Hint:
You have to prove the corresponding negation: ¬(5 ∈ small_set).
@@@ -/

example : 5 ∈ small_setᶜ := sorry


/- @@@
### Difference
@@@ -/

#reduce Set.diff
-- fun s t a => s a ∧ (a ∈ t → False)
-- fun s t a => a ∈ s ∧ a ∉ t (better abstracted expression of same idea)

example : 6 ∈ ev_set \ small_set := ⟨ rfl, λ h => nomatch h ⟩

#reduce 6 ∈ ev_set \ small_set

/- @@@
### Subset
@@@ -/

#reduce @Set.Subset
-- fun {α} s₁ s₂ => ∀ ⦃a : α⦄, a ∈ s₁ → s₂ a

/- @@@
### Product
@@@ -/

#reduce Set.prod
-- fun s t p => p.fst ∈ s ∧ p.snd ∈ t

/- @@@
### Powerset
@@@ -/

#reduce @Set.powerset
-- fun {α} s t => ∀ ⦃a : α⦄, a ∈ t → s a


/- @@@
### Powerset of Product

This set is important because its elements, being subsets
of the product set on sets s and t can be seen as representing
the set of all binary relations on these two sets. An element
of this set is isomorphic to and can be taken as specifying a
binary relation from s to t.

When mathematicians want to assume that, r is some binary
relation on sets, s and t, one can therefore write either
r ⊆ s × t, or r ∈ 𝒫 (s × t.)
@@@-/

#reduce @Set.powerset (Set.prod _ _)
-- fun s t => t ⊆ s

end DMT1.Lectures.setsRelationsFunctions.sets
