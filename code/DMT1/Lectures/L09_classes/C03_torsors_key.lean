import DMT1.Lectures.L09_classes.C02_groupActions
import Mathlib.Algebra.AddTorsor.Defs

/- @@@
# Torsors
@@@ -/

namespace DMT1.Lecture.classes.torsors
open DMT1.Lecture.classes.groupActions

/- @@@
We've seen how group elements can act on
objects. Let's now consider a special case,
where vectors in a vector space are actions,
and where they act on points in a linear space
by *displacing* (rather than, say, *rotating*)
them.
@@@ -/

#check AddTorsor

/- @@@
Paraphrasing the documentation for AddTorsor in
Lean's *mathlib* we find that an `AddTorsor G P`
gives a structure to a *nonempty* type `P`, acted on
by an `AddGroup G` with a transitive and free action
given by the `+ᵥ` operation and ... where subtraction
of *points* (torsor elements), yielding group actions,
is given by the `-ᵥ` operation. In the case where G is
a *vector space*, a torsor becomes an *affine* space.

```lean
class AddTorsor (G : outParam Type*) (P : Type*) [AddGroup G] extends AddAction G P,
  VSub G P where
  [nonempty : Nonempty P]
  /-- Torsor subtraction and addition with the same element cancels out. -/
  vsub_vadd' : ∀ p₁ p₂ : P, (p₁ -ᵥ p₂ : G) +ᵥ p₂ = p₁
  /-- Torsor addition and subtraction with the same element cancels out. -/
  vadd_vsub' : ∀ (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
```

Let's take that apart and see what we're missing.
We have *G* being our rotation group. We have *P*
being our *tribot* and its possible orientations.
We already have defined an *AddGroup* structure on
*G*, and we've already defined *AddAction, (+ᵥ)*
as the action of a rotation on an orientation. What
we're missing is an operation for *subtracting* one
*point* from another yielding the group action that
gets you from the first to the second, and we are
missing a proof that our Tri type is non-empty. So
what we must instantiate are *NonEmpty P* as well as
*VSub G P* typeclass. Then we'll have the pieces we
need to instantiate *Torsor Rot Tri*.

To complete the typeclass instance, we'll need proofs
that the *torsor laws* are followed. There are two.
The first says that if you subtract two points, the
action that results, when applied to the first point
takes you to the second point. The first says that
the action, *(p₁ -ᵥ p₂)*, when applied to *p₂* takes
you to *p_₁*.

To visualize *p₁ - p₂* select two points in a plane.
Now put an arrowhead pointing at *p₁* then draw the
line ending at that arrowhead to *p₂*. So *p₂* will
be the starting point. The arrow indicates the action
that then *translates* the point *p₂* to *p₁*. Thus
adding that arrow (applying that action), to *p₂ will
yield *p₁*.

The second torsor law says that if you have an action
*g* act on a point *p* yielding a new point *(g +ᵥ p)*,
then if from that new point you subtract the original
point, *p*, the result is just exactly the action that
got you from *p* to *g +ᵥ p*. The algebra makes sense.
@@@ -/

-- EXERCISE: Define point-point subtraction for Rot, Tri

def rotTriVSub : Tri → Tri → Rot
-- define p1 - p2
| Tri.o0, Tri.o0 => Rot.r0
| Tri.o0, Tri.o120 => Rot.r240
| Tri.o0, Tri.o240 => Rot.r120
| Tri.o120, Tri.o0 => Rot.r120
| Tri.o120, Tri.o120 => Rot.r0
| Tri.o120, Tri.o240 => Rot.r240
| Tri.o240, Tri.o0 => Rot.r240
| Tri.o240, Tri.o120 => Rot.r120
| Tri.o240, Tri.o240 => Rot.r0

-- EXERCISE: Instantiate the VSub class for Rot and Tri

instance : VSub Rot Tri :=
{
  vsub := rotTriVSub
}

-- Exercise: Instantiate NonEmpty for Tri.

/- @@@
```
class inductive Nonempty (α : Sort u) : Prop where
  | intro (val : α) : Nonempty α
```
@@@ -/

theorem nonemptyTri: Nonempty Tri :=
by
  exact Nonempty.intro Tri.o0


-- EXERCISE: Prove the first torsor law.

theorem law1 : ∀ p₁ p₂ : Tri, (p₁ -ᵥ p₂ : Rot) +ᵥ p₂ = p₁ :=
by
  intro p₁ p₂
  cases p₁
  repeat
  {
    cases p₂
    repeat rfl
  }


-- Exercise: Prove the second torsor law.

theorem law2 : ∀ (g : Rot) (p : Tri), (g +ᵥ p) -ᵥ p = g :=
by
  intro g p
  cases g
  repeat
    {
      cases p
      repeat rfl
    }


-- EXERCISE: Instantiate AddTorsor for Rot and Tri

instance : AddTorsor Rot Tri :=
{
  nonempty := nonemptyTri
  vsub_vadd' := law1
  vadd_vsub' := law2
}

-- EXERCISE: TEST CASES!

end DMT1.Lecture.classes.torsors
