import Mathlib.Algebra.Group.Defs

/- @@@
<!-- toc -->

# Groups

In abstract algebra, a group is a *mathenmatical structure*
with several elements:

 @@@

- a set of objects, sometimes called the *carrier set*
- a binary operation on elements of this set
- an element designated as the *zero* or *identity* element
- an inverse operation on elements of the set

These objects are tied together by additional constraints:

- the binary operation must be associative
- the zero element be a left and right zero for addition
- the addition of any element and its inverse must be zero

@@@ -/

namespace DMT1.Lecture.classes.groups

#check Zero
#check AddZeroClass
#check AddSemigroup
#check AddMonoid

/-
## Overloading Operations With Typeclasses
@@@ -/
#check Add

/- @@@
```
class Add (α : Type u) where
  /-- `a + b` computes the sum of `a` and `b`. See `HAdd`. -/
  add : α → α → α
```
@@@ -/

/- @@@
## Example: Rotational Symmetries of a Triangle

Think of these as the three orientations of
an equilateral triangle that sits on top of
itself. We'll have the triangle rotated zero,
one hundred twenty, and finally two hundred
forty degrees.
@@@ -/

inductive Rot : Type where | r0 | r120 | r240
open Rot

/- @@@
We will define an addition operation on
rotations in the obvious way.
@@@ -/

def addRot : Rot → Rot → Rot
| r0, r => r
| r, r0 => r
| r120, r120 => r240
| r240, r120 =>  r0
| r120, r240 => r0
| r240, r240 => r120

/- @@@
Right now we have no definition of *+*
for objects of this type.
@@@ -/
-- uncomment to see the error
--#eval r0 + r120

/- @@@
We get such a definition by defining the
*Add* typeclass for the *Rot* type. All
we have to do is provide a definition of
*Add.add* for objects of the *Rot* type.
@@@ -/
instance : Add Rot :=
{
  add := addRot
}

/- @@@
With that we can write Add.add r0 r120,
but we also gain use of notations defined
for *Add.add* in general.
@@@ -/
#eval Add.add r0 r120 -- Uses Add.add for Rot
#eval r0 + r120       -- Same thing w/ notation


/- @@@
## Additive Monoids
@@@ -/

#check AddMonoid

/- @@@
```
class AddMonoid (M : Type u) extends AddSemigroup M, AddZeroClass M where
  protected nsmul : ℕ → M → M
  protected nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  protected nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = nsmul n x + x := by intros; rfl
```
@@@ -/

#check AddSemigroup

/- @@@
## Additive Semigroups
```
class AddSemigroup (G : Type u) extends Add G where
  protected add_assoc : ∀ a b c : G, a + b + c = a + (b + c)
```

We will prove that rotation addition is associative
as a separate theorem now, and then will simply plug
that in to our new typeclass instance as the proof.
@@@ -/

theorem rotAddAssoc : ∀ (a b c : Rot), a + b + c = a + (b + c) :=
by
    intro a b c
    cases a
    -- a = ro
    {
      cases b
      -- b = r0
      {
        sorry
      }
      -- b = r120
      {
        sorry
      }
      -- b = 240
      {
        sorry
      }
    }
    -- a = r120
    {
      sorry
    }
    -- a = r240
    {
      sorry
    }

/- @@@
Now we can augment the Rot type with the
structure of a mathematical semigroup. All
that means, again, is that (1) there is an
addition operation, and (2) it's associative.
@@@ -/
instance : AddSemigroup Rot :=
{
  add_assoc := rotAddAssoc
}

/- @@@
Next, on our path to augmenting the Rot type
with the structure of an additive monoid, we
also need to have AddZeroClass for Rot. This
class will add the structure that overloads
a *zero* value and requires it to behave as
both a left and right identity (zero) for +.
@@@ -/

#check AddZeroClass

/- @@@
Here's the AddZeroClass typeclass. It in turn
requires Zero and Add for Rot.
```
class AddZeroClass (M : Type u) extends Zero M, Add M where
  protected zero_add : ∀ a : M, 0 + a = a
  protected add_zero : ∀ a : M, a + 0 = a
```

It inherits from (extends) Zero and Add. Here's the Zero
class. It just defines a value to be known as *zero*, and
denoted as *0*.
```
class Zero (α : Type u) where
  zero : α
```
@@@ -/

#check Zero

instance : Zero Rot := { zero := r0 }

#reduce (0 : Rot) -- 0 now notation for r0

instance : AddZeroClass Rot :=
{
  zero_add :=
    by
      intro a
      cases a
      repeat rfl
  add_zero :=
    by
      intro a
      cases a
      repeat rfl
}

/- @@@
We're almost prepared to add the structure of
a monoid on Rot. For that, we'll need to implement
a *natural number scalar multiplication operator*
for Rot.
@@@ -/
def nsmulRot : Nat → Rot → Rot
| 0, _ => 0   -- Note use of 0 as notation for r0
| (n' + 1), r => nsmulRot n' r + r

/- @@@
And voila, we add the structure of a Monoid
(additive) to the Rot type.
@@@ -/
instance : AddMonoid Rot :=
{
  nsmul := nsmulRot
}

/- @@@
Note that the *nsmul_zero* and *nsmul_succ* fields
have default values, proving (if possible) that *nsmul*
behaves properly. Namely, scalar multiplication by the
natural number, *0*, returns the *0* rotation, and that
scalar multiplication is just iterated addition.

With this complete definition AddMonoid for *Rot*, we
have gained a *scalar multiplication by natural number*
operation, with concrete notation, • (enter as *\smul*).

The result is an algebraic structure with *Rot* as the
carrier group, and with addition (*+*), zero (*0*), and
scalar multiplication (•) operations.
@@@ -/

#eval (0 : Rot)   -- zero
#eval r120 + 0    -- addition
#eval! 2 • r240   -- scalar mult by ℕ


/- @@@
## Additive Groups
@@@ -/

#check AddGroup

/- @@@
```
class AddGroup (A : Type u) extends SubNegMonoid A where
  protected neg_add_cancel : ∀ a : A, -a + a = 0
```

To impose a group structure on *Rot*, we will need first
to impose the structure of a *SubNegMonoid* and then add
a proof that *-a + a* is *0* for any *a*. Instantiating
*SubNegMonoid* in turn will require *AddMonoid* (which we
already have), *Neg*, and *Sub* instances to be defined,
as seen next.
@@@ -/

#check SubNegMonoid
/- @@@
Note that most fields of this structure have default values.

```
class SubNegMonoid (G : Type u) extends AddMonoid G, Neg G, Sub G where
  protected sub := SubNegMonoid.sub'
  protected sub_eq_add_neg : ∀ a b : G, a - b = a + -b := by intros; rfl
  /-- Multiplication by an integer.
  Set this to `zsmulRec` unless `Module` diamonds are possible. -/
  protected zsmul : ℤ → G → G
  protected zsmul_zero' : ∀ a : G, zsmul 0 a = 0 := by intros; rfl
  protected zsmul_succ' (n : ℕ) (a : G) :
      zsmul n.succ a = zsmul n a + a := by
    intros; rfl
  protected zsmul_neg' (n : ℕ) (a : G) : zsmul (Int.negSucc n) a = -zsmul n.succ a := by
    intros; rfl
  ```
@@@ -/

-- EXERCISE: Instantiate SubNegMonoid, thus also Neg and Sub

/- @@@
```lean
class Neg (α : Type u) where
  neg : α → α
```
@@@ -/

def negRot : Rot → Rot
| 0 => 0
| r120 => r240
| r240 => r120

instance : Neg Rot :=
{
  neg := negRot
}

/- @@@
```lean
class Sub (α : Type u) where
  sub : α → α → α
```
@@@ -/

instance : Sub Rot :=
{
  sub := λ a b => a + -b
}


instance : SubNegMonoid Rot :=
{
  zsmul := zsmulRec
}

  -- EXERCISE: Instantiate AddGroup

theorem rotNegAddCancel :  ∀ r : Rot, -r + r = 0 :=
by
  intro r
  cases r
  rfl
  rfl
  rfl

instance : AddGroup Rot :=
{
  neg_add_cancel := rotNegAddCancel
}

/-@@@
## Example: A Rotation Group

We have succeeded in establishing that the rotational
symmetries of an equilateral triangle for an additive
group. Th
@@@-/


def aRot := r120                  -- rotations
def zeroRot := r0                 -- zero element
def aRotInv := -r120              -- inverse
def aRotPlus := r120 + r240       -- addition
def aRotMinus := r120 - r240
def aRotInvTimesNat := 2 • r120   -- scalar mul by ℕ
def aRotInvTimeInt := -2 • r120   -- scalar mul by ℤ

/- @@@
Question: Can we define scalar multiplication by reals
or rationals?
@@@ -/


/- @@@
## Constraints on Type Arguments
@@@ -/

-- uncomment to see error
-- def myAdd {α : Type u} : α → α → α
-- | a1, a2 => a1 + a2

def myAdd {α : Type u} [Add α] : α → α → α
| a, b => a + b

/- @@@
By requiring that there be a typeclass instance
for α in *myAdd* we've constrained the function to
take and accept only those type for which this is
the case. We could read this definition as saying,
"Let myAdd by a function polymorphic *in any type for
which + is defined*, such that myAdd a b = a + b."

What we have thus defined is a polymorphic function,
but one that applies only to values of type for which
some additional information is defined, here, how to
add elements of a given type.
@@@ -/

#eval myAdd 1 2                   -- Nat
#eval myAdd r120 r240             -- Rot

/- @@@
We cannot use *myAdd* at the moment to add
strings, because there's no definition of the
Add typeclass for the String type.
@@@ -/
-- uncomment to see error
-- #eval myAdd "Hello, " "Lean"   -- String (nope)

/- @@@
That problem can be fixed by creating an
instance of Add for the String type, where
we use String.append to implement add (+).
With that we can now apply *myAdd* to String
arguments as well. We have to define a special
case *Add* typeclass instance for each type we
want to be addable using *Add.add*, namely *+*.
@@@ -/
instance : Add String :=
{
  add := String.append
}
#eval myAdd "Hello, " "Lean"


 end DMT1.Lecture.classes.groups
