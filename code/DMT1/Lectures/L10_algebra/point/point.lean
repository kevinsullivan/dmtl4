import Init.Data.Repr
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.AffineSpace.Defs
import Mathlib.Algebra.Module.Pi
import DMT1.Lectures.L10_algebra.tuple.tuple
import DMT1.Lectures.L10_algebra.vector.vector

namespace DMT1.Algebra.Point

open DMT1.Algebra.Vector
open DMT1.Algebra.Tuples

universe u
variable
  {n : Nat}
  {α : Type u}

------------------------------------------- POINTS
/- @@@
## Pt α n

We will now represent n-dimensional α *points* * as
n-tuples of α values in the same way.

### Data Type
@@@ -/

@[ext]
structure Pt (α : Type u) (n: Nat) where
  (toRep: Tuple α n)
deriving Repr   -- , DecidableEq --, BEq

/- @@@
### Values

There are no distinguished point values.
@@@ -/



/- @@@
### Operations
@@@ -/

/- @@@
### Add

There is no addition operation on points. Leaving out
the definition of one means that it's not even syntactic
to write p1 + p2. (We're careful not to enable coercions
to reps except with care), which would permit expressions
like this but the results would only be tuples. If there
is a check for that type distinction, great, but good
luck finding that in eeryday practice.
@@@ -/

/- @@@
### Sub

In place of Sub, we ask that ones use the heterogeneous -ᵥ
VSub) subtraction operator.
@@@ -/

/- @@@
#### Nonempty
@@@ -/

instance [Zero α] : Nonempty (Pt α n) := ⟨ ⟨ 0 ⟩ ⟩

/- @@@
#### VSub

This is the -ᵥ notation providing typeclass.
@@@ -/

instance [Sub α] : VSub (Vc α n) (Pt α n) :=
{ vsub p1 p2 := ⟨ p1.1 - p2.1 ⟩ }

-- Need notation class

@[simp]
theorem Pt.vsub_def [Sub α] (p1 p2 : Pt α n) :
  p1 -ᵥ p2 = ⟨ p1.1 - p2.1 ⟩ := rfl

/- @@@
#### VAdd (Vc α n) (Pt α n)
@@@ -/
-- defines +ᵥ
instance [Add α] : VAdd (Vc α n) (Pt α n) where
  vadd v p := ⟨ v.1 + p.1 ⟩

-- SIMP ENABLED
@[simp]
theorem Pt.vadd_def [Add α] (v : Vc α n) (p : Pt α n) :
  v +ᵥ p = ⟨ v.1 + p.1 ⟩ := rfl

-- Insight need notation eliminating rule for VAdd from HVAdd
@[simp]
theorem Pt.hVAdd_def [Add α] (v : Vc α n) (p : Pt α n) :
  v +ᵥ p = ⟨ v.1 + p.1 ⟩ := rfl

/- @@@
#### VSub then VAdd
@@@ -/

-- set_option pp.rawOnError true

-- @[simp]
theorem Pt.vsub_vadd_def
  [Add α]
  [Sub α]
  (p1 p2 : Pt α n) :
  (p1 -ᵥ p2) +ᵥ p2 = ⟨ (p1 -ᵥ p2).1 + p2.1 ⟩ := rfl

/- @@@
Key was to add def theorem for the
notation class HVadd *notation* class.
-/

-- ∀ (p₁ p₂ : Pt α n), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
/- @@@
### AddActon (Vc α n) (Pt α n)
@@@ -/

/-
/-- An `AddMonoid` is an `AddSemigroup` with an element `0` such that `0 + a = a + 0 = a`. -/
class AddMonoid (M : Type u) extends AddSemigroup M, AddZeroClass M where
  /-- Multiplication by a natural number.
  Set this to `nsmulRec` unless `Module` diamonds are possible. -/
  protected nsmul : ℕ → M → M
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  protected nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  protected nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = nsmul n x + x := by intros; rfl
-/

instance [AddMonoid α] : AddMonoid (Vc α n) :=
{
  nsmul := nsmulRec
}

instance [AddMonoid α]: AddAction (Vc α n) (Pt α n) :=
{
  --  (p : Pt α n), 0 +ᵥ p = p
  zero_vadd := by
    intro
    -- to study in part by stepping through
    --
    simp only [Pt.vadd_def]
    simp [Tuple.add_def]
    simp [Vc.zero_def]
    simp [Tuple.zero_def]

  -- ∀ (g₁ g₂ : Vc α n) (p : Pt α n), (g₁ + g₂) +ᵥ p = g₁ +ᵥ g₂ +ᵥ p
  -- GOOD EXERCISE
  add_vadd :=  by
    intros
    simp only [Pt.vadd_def]
    simp [Tuple.add_def]
    apply add_assoc
}

theorem Pt.add_vadd_def [Add α] (v1 v2 : Vc α n) (p : Pt α n) :
  (v1 + v2) +ᵥ p = ⟨(v1.1 + v2.1) + p.1 ⟩ := rfl


/- @@@
There now. Behold. Correct is simpler
@@@ -/
@[simp]
theorem Pt.vsub_vadd'_def
  [Zero α]
  [Add α]
  [Sub α]
  (p1 p2 : Pt α n) :
(p1 -ᵥ p2) +ᵥ p2 =  ⟨ p1.1 - p2.1 + p2.1⟩ :=
-- match on left pattern
-- rewrite as this pattern
by  -- and this shows it's ok
  simp only [Pt.vadd_def]
  simp only [Pt.vsub_def]

end DMT1.Algebra.Point
