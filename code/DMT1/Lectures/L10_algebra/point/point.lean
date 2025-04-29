import DMT1.Lectures.L10_algebra.vector.vector

namespace DMT1.Algebra.Point

open DMT1.Algebra.Vector
open DMT1.Algebra.Tuples

universe u
variable
  {n : Nat}
  {α : Type u}

/- @@@
# Points: Pt α n

We will now represent n-dimensional α *points* * as
n-tuples of α values in the same way.

## Representation
@@@ -/

@[ext]
structure Pt (α : Type u) (n: Nat) where
  (toRep: Fin n → α)
deriving Repr     --, DecidableEq --, BEq



/- @@@
## Values: Zero (Vc α n)
There are no distinguished point values. However
we do need proof that there's *some point*. For that
we'll require, somewhat arbitrarily, that there be a
Zero scalar, and we'll build an arbitrary point with
all zero internal parameters.
@@@ -/

instance [Zero α] : Nonempty (Pt α n) := ⟨ ⟨ 0 ⟩ ⟩



/- @@@
## Operations
@@@ -/



/- @@@
### VSub (Vc α n) (Pt α n)

This is the -ᵥ notation providing typeclass.
@@@ -/

instance [Sub α] : VSub (Vc α n) (Pt α n) :=
{ vsub p1 p2 := ⟨ p1.1 - p2.1 ⟩ }


@[simp]
theorem Pt.vsub_def [Sub α] (p1 p2 : Pt α n) :
  p1 -ᵥ p2 = ⟨ p1.1 - p2.1 ⟩ := rfl

theorem Pt.vsub_toRep [Sub α] (p1 p2 : Pt α n) (i : Fin n) :
  (p1 -ᵥ p2).toRep i = p1.toRep i - p2.toRep i := rfl



/- @@@
### VAdd (Vc α n) (Pt α n)
@@@ -/
-- defines +ᵥ
instance [Add α] : VAdd (Vc α n) (Pt α n) where
  vadd v p := ⟨ v.1 + p.1 ⟩

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

-- ∀ (p₁ p₂ : Pt α n), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
/- @@@
#### AddActon (Vc α n) (Pt α n)
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
    simp only [Pt.hVAdd_def]
    -- TODO: Release note: a simplification here, losing two lines
    --simp [Tuple.add_def]
    simp [Vc.zero_def]
   -- simp [Tuple.zero_def]

  -- ∀ (g₁ g₂ : Vc α n) (p : Pt α n), (g₁ + g₂) +ᵥ p = g₁ +ᵥ g₂ +ᵥ p
  -- GOOD EXERCISE
  -- TODO: Release note: simplification here, too
  add_vadd :=  by
    intros
    ext
    apply add_assoc
}


/- @@@
### Add then VAdd
@@@ -/

theorem Pt.add_vadd_def [Add α] (v1 v2 : Vc α n) (p : Pt α n) :
  (v1 + v2) +ᵥ p = ⟨ (v1 + v2).1 +  p.1 ⟩ := rfl


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
  simp only [Pt.hVAdd_def]
  simp only [Pt.vsub_def]

end DMT1.Algebra.Point
