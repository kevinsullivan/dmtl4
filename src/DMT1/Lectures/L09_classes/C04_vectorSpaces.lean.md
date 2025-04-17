```lean
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Module.Basic
--import Mathlib.LinearAlgebra.AffineSpace.Defs
import Mathlib.Tactic.Ring.Basic
```

<!-- toc -->

# Modules and Vector Spaces

In our work so far, we've been working with expressions
involving three types of objects:

- *scalars*, (ℕ and ℤ so far), which *scale* actions
- *actions*, so far rotations, which are *vector-like*
- *points*, namely the three values values of type Tri

If *s* a scalar, *a* is an action, and *p* a point, we
can write the expression *(s • a) +ᵥ p*, scaling the
action, *a*, by the amount, *s*, with the scaled action
then applied to rotate *p*.

We have also seen that our *Rot* actions form a *group*
under *Rot* addition. That allows us to add up actions in
the group before applying the single result to a point,
rather than having to apply actions one at a time. If the
point is a robot and each action applications uses energy,
this capability can save a lot of battery power (and time).

Our work so far has set up a crucial pattern for the next
stage in our development: we have *scalar* values that act
multiplicatively on *vector-like* objects that then act
additively on on *point-like* objects.

In this and the next chapter, we'll see how to enrich
scalars, actions, and points to define *affine spaces*.
An affine space is a set of *points* (a *torsor*) acted upon
by *vectors* from not just a *group* but a *module* in the
general case and from a *vector space*, which is where our
main interests lie for now.

The essential upgrades from our earlier work are the following:

- The scalars change from a *monoid (ℕ)* or *group (ℤ)* to a *field (ℚ)*
- The actions change from a *group* to a *module* or a *vector space*
- The point set becomes a *torsor over a vector space*

## Example

A nice example of an affine space is the 1-D *real* line, ℝ.

- The *points* on the line are represented by real numbers
- The *vectors* (differences) are represented by real numbers
- The scalars are simply the real numbers

In this section, we'll first describe, and then formally define,
an affine space space. Here's what we will require:

- The scalars, *Sc*, form a *field*
- The vectors, *Vc*, form a *module* over the scalar field
- Note that a module over a field constitutes a *vector space*
- The vectors act additively on points by *translating* them

To be concrete, suppose we have two points: *p1*, represented
by the real number *2.5,* and *p2* represented by real *3.0*.
The points on the real line form a *torsor* where the expression
*p2 -ᵥ p1* represents a *vector, v,* representing the directed
difference between the points. We'll define *v* to be the vector
represented by the real number, *3.0 - 2.5 = 0.5*. That is, it's
represented as the difference between the number representing
the two points.

Already we can see fundamental benefits arising from the types
we are superimposing on real numbers based on the types of the
objects they represent. Notably, while we can subtract one point
from another to get a vector, we cannot add two points together.
That is simply *not* an operation supported in an affine space.

To be even more concrete, suppose we're roboticists who have to
reason about time. We can do that in a type-safe way with the
structure we're setting up. Suppose we represent *time* as the
real number line. Let *p1*, the *point* in time (on that line)
that we choose to represent *3* o'clock, and and *p2* represent
*5* o'clock. The difference, *p2 -ᵥ p1* represents a *duration*,
namely *v = p2 -ᵥ p1 = *2* hours.

On the other hand, the expression, *p2 + p1*, which suggests
the *addition* of 5PM and 3PM, makes no physical sense at all.
In programming a robot, if points and durations in time are both
simply real numbers (not values of distinct types), then the type
system will not reject this physically meaningless expression.

Next, let's get scalars into the picture. Suppose *s = 2.0* is
a real number. Now the expression, *s • (p2 -ᵥ p1),* should type
check as well, and would be understood as two times the interval,
*p2 -ᵥ p1*: *4* hours.

Clearly we are computing the real number *representations* of
different types of objects using ordinary real number arithmetic
on the underlying real number representations of these objects.

Now, finally, we can write a well typed expression for the
time obtained by starting at some arbitrary point in time, say
*7:30* PM, and adding this *4* hour duration. The result will be
a new point in time, *11:30* PM. If we let *p3 = 7.5*  (7:30PM).
We can express this whole computation *(s • (p2 -ᵥ p1)) +ᵥ p3*:
two (*s*) times two hours (*p2 -ᵥ p1*) added to *7:30* (*p3*) and
thus translating that point in time to (*11:30* PM), represented
by the real number, *2.0 \* (5.0 - 3.0)) + 7.5* = 11.5*. That is
just what we wanted.

The rest of this chapter will develop the *vector space* part
of our plan. We'll finish the plan in the next chapter with
definitions of points and a torsor of such points over the
vector space defined in this chapter. To define our vector
space, in turn, requires that we specify both *scalar* and
*vector* types. We will take the rationals as our scalars,
and will define a new type, *Vc*, of vectors. So here we go.


## Scalars

In our work to date, scalars have been values from a monoid
(Nat) or a group (Int). These are values that one can use to
*scale* vector-like objects, such as rotations, which in turn
form a *group*. To have an affine space, we'll need scalars to
come from a *field* and the set of vector-like objects to form
what mathematicians call a *module*.

A module is like a vector space but slightly less constrained,
in the sense that the scalars that multiple module elements are
required to come

As we've seen, we cannot compute with real numbers. Yet we need
scalars (and the numbers we use to represent points and vectors)
to form a *field* under usual addition and multiplication. A good
compromise is to use the rationals, ℚ, as scalars. Like the reals
the rationals form a field, but they are also computable.

However, we can do better than to hardwire the choice of ℚ as our
scalar field by specifying the scalar type as a type parameter in
our development. We'll call it *K*, and we'll add the constraint
that whatever type *K* is, it must have the structure of a *field*.

That *K* forms a field means, roughly speaking, that it has addition
and multiplication operators, it forms a group under addition and if
0 is excluded it also forms a group under multiplication, and that
these operations are constrained to follow the usual *distributive*
laws.

In Lean, we express the requirement that the scalars form a field by
declaring that there must be an instance of the *Field* typeclass for
whatever type *K* is defined to be.

```lean
abbrev K := ℚ
```

Note that if you set *K* to *Nat* (not a field) you will *not* get a
type error at this point. The variable declaration asserts only the
requirement that there be such a typeclass but Lean does not verify
that that's the case at this time. Rather, it's when you try to *use*
an operation or value provided by such a typeclass, which is when Lean
tries to find an instance, that Lean will complain.

You can see this idea in action by changing *K* from ℚ to *Nat* in the
preceding definition.

```lean
def invK (a : K) := a⁻¹   -- returns the multiplicative inverse of a K
#eval invK 3              -- but fails to synthesize [Field K] if K = Nat
```

Now remember to change *K* back to meaning *Q* and all will be well.
Later on you can try changing it to ℝ.

At this point we've done everything we need to establish the rationals
as a scalar field. That was easy.




## "Vectors"

```lean
structure Vc : Type where
(val : K)

-- definition of vector (Vc) addition
def addVc (v1 v2 : Vc) := Vc.mk (v1.val + v2.val)
```

Now we want to show that the set of *Vc* objects
forms a *module*. A module is just a bit less than
a vector space, in that the scalars need only come
from a *ring*, which is a generalization of (that
is, slightly less constrained than) a field, in
that a ring need not have multiplicative inverses.

We will show that *Vc* can be endowed with the added
structure of a module by instantiating Lean's *Module*
typeclass for the type, *Vc*.

## Modules

```lean
#check Module
```

Here's the *Module* typeclass type:
```lean
Module.{u, v} (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] : Type (max u v)Lean 4
```

The two steps that are required here are, first, we have
to show that our scalar type, K := ℚ (the actual parameter
we will use for *R* in the Module type definition) has the
structure of a *semiring* (whatever that is). We do that by
providing a Semiring typeclass instance for *K* which is to
say for *ℚ*. Similarly we have to provide an AddCommMonoid
typeclass instance for *Vc* (the actual parameter for *M*).

Lean's libraries already have proven that ℚ is a semiring
by providing a typeclass instance for us. We can either
write *instance : Semiring K := {}* or use the *variable*
construct, as we did above, to tell Lean that we require
and assume there is such a typeclass instance.
```lean
-- variable [Semiring K]
-- TODO: Fix that and above
```

The other typeclass instance we need is *AddCommMonoid Vc*.
*AddCommMonoid*, like many typeclasses, extends (essentially
inherits from) other finer-grained typeclasses, with the end
result being a typeclass with multiple fields, some inherited
and some added.

We could define an *AddCommMonoid Vc* instance by explicitly
defining instances of all of the typeclasses *AddCommMonoid*
extends. An easier way is to use Lean's error reporting to see
what overall set of elements we need to define. Once you have
provided required instances, write an empty *AddCommMonoid Vc*
structure (using curly braces) and check the error message. It
will tell you what fields you're missing. Next, add the fields
and stub out the values using sorry. Finally provide the actual
values needed. In this way you can avoid the tedium of tracking
down and instantiating all of the parent typeclasses.

```lean
instance : Zero Vc := { zero := Vc.mk 0 }
instance : Add Vc := { add := addVc }

instance : AddCommMonoid Vc :=
{
  add := addVc      -- we had to define Vc addition
  add_assoc := by   -- we need a proof it's associative
    intro a b c     -- assume a, b, c are Vc's
```
Our goal now is to show *a + b + c = a + (b + c)*.
To do this, we need to show that the rational
numbers representing the vectors on either side
of the equals sign are the same. And to do that,
we need to get at the rational numbers that are
the underlying representations of these vectors.

For this, we will use the theorem, provided by
Lean, called *congrArg*. It shows that if *f* is
any function and *a = b* then *f a = f b*. So if
you need to show that *f a = f b* it will suffice
to show that *a = b*. Given two vectors (Vc), we
can thus show that they're equal by showing that
their rational number representations are equal.
These are the arguments given to *Vc.mk* when the
objects were defined). Finally, if what you need
to prove is *Vc.mk a = Vc.mk b* it will suffice
to apply *congrArg* to *Vc.mk* (our actual value
for *f*) and then to prove *a = b*. When you study
the effect of this application, you'll see that it
in effect rewrites the vectors on the left and the
side of the equality as applications of *Vc.mk* to
underlying *rational* values. The representations
of the vectors are thus exposed, and now all that
is needed is to show that these rationals are equal.
```lean
    apply congrArg Vc.mk
```
Note that the *+* in the expression, *a + b* within
parentheses in the goal is *Vc* addition, but the *+*
between the *.val* expressions is *rational* addition.
Lean already know that that's associative, so all we
have to do now is to apply Lean's general theorem
(*Rat.add_assoc*) to this special case to finish off
the proof.
```lean
    apply Rat.add_assoc

  zero := Vc.mk 0

  zero_add := by
    intro a               -- assume a is any Vc
    apply congrArg Vc.mk  -- expose representations
    simp                  -- simp works as it knows about Rat.add
    rfl                   -- same Vc, written differently, on each side

  add_zero := by
    intro a
    apply congrArg Vc.mk
    simp
    rfl
```

  At this point, you really will have to go back
  to just before this typeclass instance definition
  and define typeclass instances for *Zero Vc* and
  for *Add Vc*. When you come back here, the error
  should be resolved.
```lean
  nsmul := nsmulRec

  add_comm := by
    intro a b
    apply congrArg Vc.mk
    apply Rat.add_comm
}
```

There! With the constraints on the *K* and *Vc*
types required by *Module* now proven, we can now
take the second step and instantiate *Module K Vc*
by filling in values for each of its fields. Hover
over the error to have Lean tell you what fields
are missing. Add them, initially stubbing them out
with *sorry*. Then go back and fill in the right
values and proofs. That's it. You can write the
required values inline, or write definitions just
before this instance declarations and then use the
values inline. For example, it'd be a good idea to
define *smul* as a standalone function. This is the
operaton of multiplication (scaling) of a vector,
*v*, by  a scalar, *k*, still denoted as *k • v*.

EXERCISE
```lean
def smulKVc (k : K) (v : Vc) : Vc := Vc.mk (k * v.val)
```

To finish off the instance definition establishing
*Vc* as a *module over the field, K*, i.e., with its
scalars coming from *K*, we will first need to build
a Semiring structure on *K*. That means that the usual
distributive laws and the laws for multiplication by 1
and 0 hold. For example, we will have to show that
*∀ (a b c : ℚ), a \* (b + c) = a \* b + a \* c.* To do
this we assume *a, b, c* are arbitrary values of type
*Q*, then we show that *a * (b + c) = a * b + a * c.*

The las part is greatly facilitated by the *ring*
tactics, *ring* and *ring1*. Their superpower is to
reduce expressions using the ring operators, *+* and
*\**, to *normal* (fully reduced) forms. Here they
do that to both the left and the right side of the
goals in the following proofs, at which point *ring1*
sees that the two sides are equal and applies *rfl*.

```lean
instance : Semiring K :=
{
  left_distrib := by
    intro a b c
    ring1

  right_distrib :=  by
   sorry

  zero_mul := by
    sorry

  mul_zero := by
    sorry
}

instance : Module K Vc :=
{
  smul := smulKVc

  one_smul := by
    -- assume arbitrary (v : Vc)
    intro v
    -- expose the underlying ℚ representations
    apply congrArg Vc.mk
    -- simplify using rational number arithmetic
    simp

  mul_smul := by
    -- assume x, y are scalars
    intro x y
    -- assume v is a vector
    intro v
    -- expose representations
    apply congrArg Vc.mk
    -- Unfold • to smulVc by giving a definitionally equal goal
    -- Use the change tactic the rewrite the goal to an equal one
    change x * y * v.val = x * (smulKVc y v).val
    -- *Now* we can simplify the goal using the definition of smulKVc
    simp [smulKVc]
    -- The rest is just (rational) arithmetic for which ring1 works
    ring1

  -- ∀ (a : K), a • 0 = 0
  smul_zero := by
    -- assume arbitrary vector, a
    intro a
    -- rewrite • as prefix smulKVc and (0 : Vc) as Vc.mk 0
    change smulKVc a (Vc.mk 0) = Vc.mk 0
    -- now Lean can simplify using the definition of smulKVc
    simp [smulKVc]

  smul_add := by
    sorry

  add_smul := by
    sorry

  zero_smul := by
    sorry
}
```

## Vector Spaces

Hooray! We've now established that *Vc* forms a *module*
under scalar multiplication by rationals. And because the
rationals form not just a *ring* (in which case we'd still
have a nice *module), but a *field*, we have a vector space!

```lean
def v1 : Vc := ⟨3.5⟩
def v2 : Vc := ⟨5.5⟩
def v3 := v1 + v2         -- expect ⟨9⟩
def v4 := (2.0 : K) • v3  -- expect ⟨18⟩

#eval v3          -- 9
#eval! v4         -- 18 (delete ! when sorrys are gone)
```

We haven't yet overloaded the inverse or subtraction
operators for *Vc*. So the following expressions will
not be accepted. Uncomment them to see the error.

```lean
-- def v5 := -v4
-- def v6 := v3 - v2
```

This problem is easy to fix: overload these operators
```lean
instance : Neg Vc := { neg := fun v => (-1 : K) • v}
instance : Sub Vc := { sub := fun v2 v1 => ⟨ v2.val - v1.val ⟩ }
```

Now it works.
```lean
def v5 := -v4
def v6 := v3 - v5
```

Note also that even though we've concrete *represented*
a vector as a rational number, we can't add rations and
vectors, as that's not an operation that makes any sense
and we haven't defined such an operation. Uncomment the
following line to see the error.

```lean
-- #eval (3/2 : ℚ) + v5    -- no heterogeneous rat + vc op
-- #eval v5 + (3/2 : ℚ)    -- no heterogeneous vc + rat op
```

As a final step, to gain the notations provided by the
AddGroup typeclass, we'll instantiate it for our *Vc* type.
That will requireOur goal now is show proofs that our definitions satisfy a few
more simple axioms. You can finish the proofs.

[EXERCISE] Replace the sorry's with valid proofs.
```lean
theorem neg_add_cancelVC : ∀ (a : Vc), -a + a = 0 :=
sorry

theorem sub_eq_add_negVc : ∀ (a b : Vc), a - b = a + -b :=
sorry

instance : AddGroup Vc :=
{
  zsmul := zsmulRec
  neg_add_cancel := neg_add_cancelVC
  sub_eq_add_neg := sub_eq_add_negVc
}
```

So there we have it. An 1-dimensional rational vector
space, for which we've also instantiated *AddGroup* which
we'll need in the next chapter.
