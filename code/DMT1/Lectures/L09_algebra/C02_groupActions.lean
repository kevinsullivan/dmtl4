import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Action.Defs

import DMT1.Lectures.L09_algebra.C01_groups

namespace DMT1.Lecture.classes.groupActions

open DMT1.Lecture.classes.groups


/- @@@

<!-- toc -->

# Group Actions

Mathematicians often think of the elements of a group as
constituting *actions,* that *act/operate* on *objects,*
or *points*, to transform them into other objects/points.
For example, we can now view rotations as actions on points
corresponding to the three possible robot orientations.

Suppose, for example, that we have a robot vacuum cleaner
in the shape of an equilateral triangle, that is capable
of rotating but only in multiples of 120 degrees. It can
take only three possible orientations, in each of which the
shadow underneath it the is exactly the same as in any of
the other orientations. Mathematically, we're talking about
the *rotational symmetries* of an equilateral triangle. The
natural numbers mod three is another good model for the set
of rotations.

We will call this kind of robot a *tribot*. The state of a
tribot is its orientation: *o0* for the orientation 0 degrees
from its start state; *o120* for the orientation 120 degrees
rotated from that state (counterclockwise); and *o240* is the
orientation point 240 degrees from the initial point.
@@@ -/

/- @@@
## Orientations
@@@ -/

inductive Tri where
| o0
| o120
| o240

open Tri


/- @@@
Just as we can have additive and multiplicative groups
(depending on whether the operator acts like + or like
*), we can have additive and multiplicative group actions.
We will treat rotations as additive actions. Actions add
up to new actions. Moreover, actions operate additively
on orientations in our system. In effect we can add a
rotation to a robot in one orientation to make it turn to
a new orientation, different from the original orientation
by exactly that action.  If *r* is a rotation and *t* is a
robot, we will now write *r +ᵥ t* to express the concept of
the additive action of *r* on *t*, *adding* to its orientation
by exactly the amount of that action.
@@@ -/


/- @@@
## Rotations
@@@ -/

def vaddRotTri : Rot → Tri → Tri
| 0, t => t
| Rot.r120, o0 => o120
| Rot.r120, o120 => o240
| Rot.r120, o240 => o0
| Rot.r240, o0 => o240
| Rot.r240, o120 => o0
| Rot.r240, o240 => o120

theorem vaddZero: ∀ p : Tri, vaddRotTri (0 : Rot) p = p :=
by
  intro t
  cases t
  repeat rfl

theorem vAddSum:  ∀ (g₁ g₂ : Rot) (p : Tri), vaddRotTri (g₁ + g₂) p = vaddRotTri g₁ (vaddRotTri g₂ p) :=
by
  intro g₁ g₂ p
  cases g₁
  cases g₂
  cases p
  rfl
  repeat sorry

#check VAdd

/-
class VAdd (G : Type u) (P : Type v) where
  /-- `a +ᵥ b` computes the sum of `a` and `b`. The meaning of this notation is type-dependent,
  but it is intended to be used for left actions. -/
  vadd : G → P → P
-/

instance : VAdd Rot Tri :=
{
  vadd := vaddRotTri
}

/- @@@
```lean
class AddAction (G : Type*) (P : Type*) [AddMonoid G] extends VAdd G P where
  /-- Zero is a neutral element for `+ᵥ` -/
  protected zero_vadd : ∀ p : P, (0 : G) +ᵥ p = p
  /-- Associativity of `+` and `+ᵥ` -/
  add_vadd : ∀ (g₁ g₂ : G) (p : P), (g₁ + g₂) +ᵥ p = g₁ +ᵥ g₂ +ᵥ p
```
@@@ -/

instance : AddAction Rot Tri :=
{
  zero_vadd := vaddZero
  add_vadd := vAddSum
}

#eval Rot.r120 +ᵥ Tri.o0                -- o120
#eval Rot.r120 +ᵥ (Rot.r120 +ᵥ Tri.o0)  -- o240
#eval (Rot.r120 + Rot.r120) +ᵥ Tri.o0   -- 0240

/- @@@
Group actions must have this property that you can
add them up in the group (+) then *apply* them once
(+ᵥ) rather than applying each one in turn using +ᵥ.
That's a great way to optimize batter power usage in
a floor-vacuuming robot.
@@@ -/

end DMT1.Lecture.classes.groupActions
