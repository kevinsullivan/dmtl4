/- @@@

# Heterogeneous Collections (Lists, Tuples, etc.)

EARLY DRAFT: STILL DEVELOPING.

We've seen that parametric polymorphism enables specialization
of definitions for argument values of any type, given as the value
of a formal parameter, (α : Type u). Such a specialized definition
then pertains and applies to values of any given actual parameter
values of that that type, but only of that type. For this construct
to work well, the fixed code of such a parameterized definition has
to work for objects of any type. The code cannot encode special case
logic for different types of objects. In Lean, one cannot match on,
which is to say, distinguish, different types at all. That would
make the logic unsound. Details on that can be found elsewhere.

Constructs like these are good for representing type-homogenous
definitions. For example, (List Nat) is the type of lists all of
the elements of which are necessarily, in this case, Nat. The
generalization of this special case is (List (α : Type u)), where
α is the type of *all* elements in any list value of type (List α).

Parametric polymorphism provides a lot of leverage, but is has its
limits. Sometimes we want to generalize concepts, such as addition,
for example, following certain intuitive rules, over objects of ad
hoc types. For example, we might want a function that implements
*add* for *Nats* and, of course, a necessarily different function
that implements *add* for Rats. We've already seen that overloading
of proof-carrying structures enables compelling formalizations of
at least some useful parts of the universe of abstract mathematics.
There's ample evidence from others

With typeclasses defined to capture the abstract concepts and their
instances providing implementations of these concepts for different
types of underlying objects, and with a notation definition, we can
write both (2 + 3) and ("Hello" + "world"), with  Lean figuring out
which instance implements + (add) for Nat, and which, for String.

These method provide a form of polymorphism narrower in range than
the parametric variety, insofar as one needs to implement the full
concept for each type of underlying object (e.g., Nat or String).
But is eliminates the constraint to uniformity of implementation,
and thereby greatly augments one's expressive power.

In the context of our encounter with typeclasses, instances, and
their applications in basic abtract algebra, we met another break
from type homogeneity, in vivid distinctions between homogenous
and homogeneous variants of the "same (and even more abstracted)"
concept. Addition of two scalars is type-homogenous, but addition
of a vector to a point is heterogeneous. In the formalization we
get from Lean, one version of the addition concept (+) is defined
by the Add, with Add.add taking and returning values of one type,
whereas the other (+ᵥ) is required to be used for addition of an
object of one type to an object of another, as in the case of
vector-point addition in affine spaces. Heterogeneity of this kind
is achieved through typeclass definitions parametrically polymorphic
in multiple types.

In this chapter we consider type heterogeneity in finite collections
of objects, such as lists or tuples represented as functions from a
natural number index set to the values at those indices. What if we
want a different type of value at each position in a tuple? It's not
a remotely crazy idea: we have databases full of tables with columns
having different types of data in them. It would be good to be able
to ensure that records (tuples of values) have corresponding types.
For example, if the type labels on columns were Nat, String, Bool,
we'd want to type-check corresonding value tuples, e.g., accepting
(1, "hi", true) but rejecting anything not a 3-tuple of values of
the specified types. Another application could be in representing
function type signatures and type-checked constructors for actual
parameteter value tuples.

AI Disclosure: The author did interact with ChatGPT, with context
provided by earlier, unrelated chats, when deciding how to populate
and organize parts of this chapter. I did adopt--and in most cases
fixed--some elements of the chat output. One cannot know the real
provenance of such outputs. I take responsibility for checking of
correctness. Should you recognize some clear derivative of your
own work in this chapter, please don't hesitate to let me know.

With that long intruction, the rest of this chapter presents six
somewhat different attacks on the same basis problem, noting some
of the strengths, weaknesses, and use case of each approach (that
right there does sound like ChatGPT, doesn't it).
cases.

<!-- toc -->
@@@ -/
