import Mathlib.Algebra.Group.Defs

/- @@@
Parametric polymorphism vs Ad hoc polymorphism
@@@ -/

/- @@@
 class Mul (α : Type u) where
  -- `a * b` computes the product of `a` and `b`.
  mul : α → α → α
@@@ -/

#check Mul

#check Add

/- @@@
```
class Add (α : Type u) where
  /-- `a + b` computes the sum of `a` and `b`. See `HAdd`. -/
  add : α → α → α
```
@@@ -/

#check Zero

/- @@@
```
class Zero (α : Type u) where
  /-- The zero element of the type. -/
  zero : α
```
@@@ -/

inductive Rot : Type where | r0 | r120 | r240
open Rot


def addRot : Rot → Rot → Rot
| r0, r => r
| r, r0 => r
| r120, r120 => r240
| r240, r120 =>  r0
| r120, r240 => r0
| r240, r240 => r120


instance : Add Rot :=
{
  add := addRot
}

#eval r0 + r120


/- @@@
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
```
class AddSemigroup (G : Type u) extends Add G where
  protected add_assoc : ∀ a b c : G, a + b + c = a + (b + c)
```

We will prove that rotation addition is associative
as a separate theorem now, and then will simply plug
that in to our new typeclass instance as the proof.

HOMEWORK/EXERCISE.

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
-/

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

#reduce (0 : Rot) -- 0 is notation for r0

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
We're almost prepared to impose the structure of
a monoid on Rot, but we'll need to implement the
*natural number scalar multiplication operator* for
Rot, called *nsmul* here.
@@@ -/

def nsmulRot : Nat → Rot → Rot
| 0, _ => 0   -- Note use of 0 as notation for r0
| (n' + 1), r => nsmulRot n' r + r


/- @@@
And voila, we add the structure of a Monoid
to the Rot type.
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

#eval (0 : Rot)
#eval r120 + 0
#eval 2 • r120


/- @@@
## Type Constraints via Implicit Typeclass Instances
@@@ -/


-- uncomment to see error
-- def myAdd {α : Type u} : α → α → α
-- | a1, a2 => a1 + a2

def myAdd {α : Type u} [Add α] : α → α → α
| a1, a2 => a1 + a2

#eval myAdd 1 2                   -- Nat
#eval myAdd r120 r240             -- Rot
-- uncomment to see error
-- #eval myAdd "Hello, " "Lean"   -- String

instance : Add String :=
{
  add := String.append
}
#eval myAdd "Hello, " "Lean"

/- @@@
### Group
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
  -/
