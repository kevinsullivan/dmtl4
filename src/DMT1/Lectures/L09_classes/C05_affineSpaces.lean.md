```lean
import DMT1.Lectures.L09_classes.C04_vectorSpaces
```

<!-- toc -->

# Torsors over Modules: Affine Spaces

An *affine space* is a *torsor (a set of points) acted on
by elements of a *module*. A module is a set of vector-like
elements (for us, actions) over a scalar *ring* or *field*.
A ring is a structure with addition, additive inverses, and
multiplication, but not necessarily multiplicative inverses.
Without a multiplicative inverses, a ring lacks fractions, as
a fraction *a/b* is really just (a * b⁻¹).

## The Plan

Here we will define an affine space comprising a torsor over
a *vector space*, which in turn is a module over not just any
ring but over a scalar *field*. Moving from a scalar ring to
a scalar field ensures that all *fractions of actions* are in
the vector space.

The rationals form a field. If we take the rationals as the
scalars for a module, and if we pick a module element, we can
*scale* it by any rational (fractional) amount. This is not the
case for modules having merely scalar *rings*.

We will now illustrate these ideas by formally specifying a
1-D rational affine space. Think of it as a real number line
with points that correspond the rationals. Vectors correspond
to directed differences between pairs of rationals, and thus
also correspond to the rationals. One can subtract points to
get vectors, and one can add vectors to points to transform
them by *translating* them linearly.

```lean
abbrev
  AffineSpace           -- and affine space with
    (k : Type*)         -- scalars
    (V : Type*)         -- vectors
    (P : Type*)         -- points
    [Ring k]            -- where scalars have + and *,
    [AddCommGroup V]    -- vector addition commutes, and
    [Module k V] :=     -- vectors form a *module* over k, is a
  AddTorsor V P         -- torsor with P points and V vectors
```

In Lean, an *AffineSpace* is just another name for an additive
torsor (AddTorsor) over a module with scalars of some type, *K*,
vector-like actions of some type *V*, and points of some type,
*P*, where *K* is at least a *ring*, *V* is at least an additive
and commutative *group* (as in our group of rotational actions),
with point-point subtraction and vector-point addition operations,
satisfies additional torsor axioms.

## Formal Specification

Our 1-D affine space will be a torsor of points, conceptually on
the *rational number line* and concretely represented by rational
numbers, over a space of 1-D vectors, represented by rationals, and
with scalars also being just the rationals. Our design, with each
of these kinds of elements having different types, will ensure that
algebraically invalid expressions, e.g., addition of *points*, will
never pass the Lean type checker.

To being with, we need to define a *point* type sufficiently rich
to represent all points *reachable* by the addition of any vector
to any point. To this end it will suffice to represent our points
as rational numbers, but wrapped in a new point *type*, here *Pt*.

```lean
structure Pt : Type where (val : K)
```

With that, we're set to proceed to define our torsor of *Pt*
points over the 1-D rational vector space from the last section.
We'll do this by instantiating the *AddTorsor* typeclass for our
*Vc* and *Pt* types. That will require us to give definitions of
the torsor operations (-ᵥ and +ᵥ), and proofs that everything we
have specified satisfies the torsor axioms. Working bottom-up,
we now provide these function definitions and proofs, and then
the final affine space definition.

The set of points of a torsor cannot be empty.
```lean
instance : Nonempty Pt := ⟨Pt.mk 0⟩
```

We define a vector-point addition operation and use it to
instantiate the *VAdd* typeclass for *Vc* and *Pt*, giving
us, among other things, the *+ᵥ* notation.

```lean
def vaddVcPt (v : Vc) (p : Pt) := Pt.mk (v.val + p.val)
instance : VAdd Vc Pt := { vadd := vaddVcPt }
```

We similarly define our point-point subtraction operation
and instantiate the *VSub* typeclass get the *-ᵥ* notation.
```lean
def vsubVcPt (p1 p2 : Pt) : Vc := ⟨ p1.val - p2.val ⟩
instance : VSub Vc Pt := { vsub := vsubVcPt}
```

Here are two tests to confirm that we now have both of
these operations with corresopnding concrete notations.
```lean
#check fun (v : Vc) (p : Pt) => v +ᵥ p
#check fun p1 p2 => p1 -ᵥ p2
```

We need to prove that our definitions satisfy the torsor
axiom requiring that adding the zero vector to any point
leaves the point unchanged.
```lean
theorem zero_vaddVcPt : ∀ (p : Pt), (0 : Vc) +ᵥ p = p :=
by
    intro a
    apply congrArg Pt.mk
    simp [vaddVcPt]
    rfl

theorem add_vaddVcPt : ∀ (g₁ g₂ : Vc) (p : Pt), (g₁ + g₂) +ᵥ p = g₁ +ᵥ g₂ +ᵥ p :=
by
    intro g1 g2 h
    apply congrArg Pt.mk
```
    Here we apply a generalized theorem from Lean's libraries to
    finish the proof. The theorem is universally quantified and so
    can be treated as a function, applied to particular, to yield
    a proof about them. This is just ∀ elimination, also known as
    universal *specialization*.
```lean
    apply Rat.add_assoc

-- [EXERCISE: Finish the following proofs.]

theorem vsub_vadd'VcPt : ∀ (p₁ p₂ : Pt), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁ :=
sorry

theorem vadd_vsub'VcPt : ∀ (g : Vc) (p : Pt), (g +ᵥ p) -ᵥ p = g :=
sorry

open Affine

instance : AffineSpace Vc Pt :=
{
   zero_vadd := zero_vaddVcPt
   add_vadd := add_vaddVcPt
   vsub := vsubVcPt
   vsub_vadd' := vsub_vadd'VcPt
   vadd_vsub' := vadd_vsub'VcPt
}
```

## Test and Demonstration

And that's it. We now have a 1-D rational affine
space. Here are examples of expressions that we can
now write, with comments connecting the mathematics
to a physics scenario where points represent points
in *time* and vectors represent *intervals* between
times. Points in time can be subtracted to produce
intervals; intervals can be scaled by any rationals;
and intervals can be added to points in time yielding
new points in time.

```lean
def p1 : Pt := ⟨ 7/2 ⟩      -- 3:30 PM
def p2 : Pt := ⟨ 11/2 ⟩      -- 5:30 PM
def d1 := p2 -ᵥ p1          -- 2 hours
def d2 := ((2 : ℚ) • d1)  -- 4 hours
def p3 := d2 +ᵥ p1          -- 7:30 PM
#eval! p3                   -- 15/2 (7:30)
```

The eval command won't work here until all relevant
*sorry* terms are resolved. The *!* tells Lean to go
ahead and try anyway, which it does sucessfully. You
may, if you wish, remove the *!* once everything else
is working.




## Definitional vs. Propositional Equality

We can see in the preceding example, using eval,
that our code is computing the right value for
*p3*, namely ⟨ 15 / 2 ⟩. We thus might expect
that the proposition, *p3 = ⟨15/2⟩* would easily
be proven by rfl. Yet as the following example
shows (uncomment the code) rfl doesn't work in
this case.

```lean
-- rfl doesn't work!
-- example : p3 = ⟨ 15/2 ⟩ := rfl
```

We thus arrive at a significant complexity in type
theory: the distinction between *definitional* and
*propositional* equality propositions. Definitional
equalities are provable by *Eq.refl*, and any such
proof works by expanding definitions and applying
functions before deciding whether the terms on both
sides of the *=* are exactly the same term.

As an example, we can prove 2 + 3 = 5 because Nat
addition is a recursively defined function that can
just be applied to 2 and 3 to reduce the term 2 + 3
to 5. We'd say that 2 + 3 is *definitionally equal*
to 5.

Now consider the proposition, involving rationals:
*4/2 + 6/2 = 10/2*. Uncommenting the next example
will show that it is *not* provable using *rfl*.

```lean
-- uncomment this example to see the error
-- example: (4/2 : ℚ) + 6/2  = 10/2 := rfl
```

What the error message is saying is that Lean is
*not* able to reduce the expression on the left to
be the same as the one on the right. The problem is
that, unlike purely computable natural numbers in
Lean, rational numbers include proof terms.

Here are the fields in a structure representing a
rational number in Lean. There's a possible negative
(integer) numerator and a natural number denominator.
So far, so good. But such a structure also includes
two proof terms.

```lean
  num : ℤ
  den : ℕ
  den_pos : 0 < den
  red : Nat.coprime num.natAbs den
```

The first proof term ensures that a denominator can
never be zero. The second ensures that the numerator
and denominator are co-prime: represented *in lowest
(reduced) terms*. For example, *3/6* is represented
as *1/2* internally with a proof that *2 ≠ 0* (in the
rationals) and a proof showing that *1* and *2* have
no common factors and so can not be further reduced.

The upshot of all this is that even simple operations
on rationals, such as addition, must not one *compute*
new numerator and denominator values, but also involves
constructing proofs that the result satisfies the two
extra *logical* requirements. That is *not* something
that can be done automatically in general. There is a
lot more to it than desugaring notations, expanding
definitions, computing function values, etc,

What you have to do instead is to prove propositional
equalities on your own. Here we give a proof that *p3*
is indeed equal to ⟨ 15/2 ⟩.

This proof has two basic parts. The first part, here using
unfold and simp, *unfolds* definitions and simplifies function
application expressions using *simp*. The crucial objective
here is to eliminate notations, typeclass field applications,
and other such elements to express the goal as a pure rational
number computation. The second part uses the valuable tactic,
*norm_num*, to automate the arithmetic computation, including
the construction of the proof terms required to assemble the
final rational number term.

```lean
example :  p3 = ⟨ 15/2 ⟩ := by
  -- manually reduce goal to pure rational number arithmetic
  unfold p3
  unfold d2 p1
  unfold d1
  unfold p1 p2
  simp [VSub.vsub]
  simp [vsubVcPt]
  simp [HSMul.hSMul]
  simp [SMul.smul]
  simp [smulKVc]
  simp [HVAdd.hVAdd]
  simp [VAdd.vadd]
  simp [vaddVcPt]
  -- use the norm_num tactic to finish off the proof
  norm_num
```

As a final comment, you've now seen the *change* tactic.
It let's you change the current goal in proof construction
to a different one but only if the two are *definitionally
equal*. If Lean can confirm that, the change is accepted.
If if cannot confirm that, e.g., because doing so would
require proof construction, then the change will not be
allowed, even if it's a perfectly mathematically valid
rewriting of the goal.
