```lean
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Action.Defs

import DMT1.Lectures.L09_classes.C01_groups
```


<!-- toc -->

<!-- toc -->
# Group Actions

Mathematicians of think of the elements of a group as
constituting *actions* that can be applied to *objects*
of some other type.

For example, we can now consider rotations as actions
on some kind of object, such as a vaccum robot: on that
can rotate to change its direction of travel. Such a
rotation *acts* on an object by *rotating* it by some
defined amount.

To make the idea concrete, suppose we have a kind of
floor vacuuming robot. It's very silly looking, as it
is in the shape of an equilateral triangle, and it is
limited in that it can point only in three directions,
namely those of its three points. We will call this kind
of robot a *tribot*, and we will designate the *state*
of a tribot as its orientation: o0 for orientation 0
degrees from its start state; o120, rotated 120 degrees
from that state; and o240, rotated 240 degrees.

The idea then is that we will have triangular robots;
we will have our group of rotation *actions*; and we
will be able to compute a robot's new state when it is
acted upon by a rotation.

Let's define our triangular robot type.

```lean
namespace DMT1.Lecture.classes.groupActions

open DMT1.Lecture.classes.groups

inductive Tri where
| o0
| o120
| o240

open Tri
```


Just as we can have additive and multiplicative groups
(depending on whether the operator acts like + or like
*), we can have additive and multiplicative group actions.
We will consider rotations to be additive actions. We add
a rotation to a robot to make it turn to a new orientation.
If *r* is a rotation and *t* is a robot, we will now write
*r +ᵥ t* as the additive action of *r* on *t* returning a
new robot state.

In Lean, the general concept of an additive group action
is specified by the AddAction typeclass. Instantiating this
class will provide the +ᵥ notation, shorthand for *vadd,*
the operation that will apply an action to an object. This
typeclass will turn rotations into actions on robots.

```lean
#check AddAction
```

```lean
class AddAction (G : Type*) (P : Type*) [AddMonoid G] extends VAdd G P where
  /-- Zero is a neutral element for `+ᵥ` -/
  protected zero_vadd : ∀ p : P, (0 : G) +ᵥ p = p
  /-- Associativity of `+` and `+ᵥ` -/
  add_vadd : ∀ (g₁ g₂ : G) (p : P), (g₁ + g₂) +ᵥ p = g₁ +ᵥ g₂ +ᵥ p
```

We can see that the *AddAction* typeclass is parameterized by two
types: *G* and *P*. *G* will be our group of actions (here required
only to be a monoid). *P* will be the type of objects acted upon.
To instantiate the class, we will need three elements:

- an instance of the *VAdd* class, defining (overloading) +ᵥ
- show that the group zero element is "no action"
- show that applying a sum of actions is the same as one at a time

```lean
open Rot

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
```

```lean
class AddAction (G : Type*) (P : Type*) [AddMonoid G] extends VAdd G P where
  /-- Zero is a neutral element for `+ᵥ` -/
  protected zero_vadd : ∀ p : P, (0 : G) +ᵥ p = p
  /-- Associativity of `+` and `+ᵥ` -/
  add_vadd : ∀ (g₁ g₂ : G) (p : P), (g₁ + g₂) +ᵥ p = g₁ +ᵥ g₂ +ᵥ p
```

```lean
instance : AddAction Rot Tri :=
{
  zero_vadd := vaddZero
  add_vadd := vAddSum
}

#eval Rot.r120 +ᵥ Tri.o0                -- o120
#eval Rot.r120 +ᵥ (Rot.r120 +ᵥ Tri.o0)  -- o240
#eval (Rot.r120 + Rot.r120) +ᵥ Tri.o0   -- 0240
```

Group actions must have this property that you can
add them up in the group (+) then *apply* them once
(+ᵥ) rather than applying each one in turn using +ᵥ.
That's a great way to optimize batter power usage in
a floor-vacuuming robot.

```lean
end DMT1.Lecture.classes.groupActions
```
