import Init.Data.Repr
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.AffineSpace.Defs
import Mathlib.Algebra.Module.Pi
import DMT1.Lectures.L10_algebra.Tuple.tuple

open DMT1.Algebra.Tuple

namespace DMT1.Algebra.Vector

universe u
variable
  {n : Nat}
  {α : Type u}

----------------------------------------------------
/- @@@
# Vector: Vc α n

We now define our abstract vector type, *Vc α n*, in
the same way, but now using *Tuple α n* as a concrete
representation. We lift the operations and structures
we need from the underlying *Tuple* type, just as did
for *Tuple* from he underlying scalar *K* type.
@@@ -/

/- @@@
### Data
@@@ -/

@[ext]
structure Vc (α : Type u) (n : Nat) : Type u where
  (toRep : Tuple α n)
deriving Repr

/- @@@
### Values
@@@ -/

instance [Zero α]: Zero (Vc α n) where
  zero := ⟨ 0 ⟩

-- @[simp]
theorem Vc.zero_def [Zero α] :
  (0 : Vc α n) = ⟨ ( 0 : Tuple α n) ⟩ := rfl


/- @@@
### Operations
@@@ -/


/- @@@
#### Add
@@@-/

instance [Add α] : Add (Vc α n) where
  add t1 t2 := ⟨ t1.1 + t2.1 ⟩


-- SIMP ENABLED HERE
theorem Vc.add_def [Add α] (t1 t2 : Vc α n) :
  t1 + t2 = ⟨ t1.1 + t2.1 ⟩ := rfl

/- @@@
#### HAdd
@@@-/

-- Support for Vc `+` notation using HAdd
@[simp]
instance [Add α]  : HAdd (Vc α n) (Vc α n) (Vc α n) :=
{ hAdd := Add.add }

@[simp]
theorem Vc.hAdd_def [Add α] (v w : Vc α n) :
  HAdd.hAdd v w = ⟨ v.1 + w.1 ⟩ := rfl

/- @@@
#### VAdd
@@@ -/

/- @@@
#### VAdd (Vc α n) (Vc α n)

Question need for this, and design appropriateness.

-- defines +ᵥ on *vectors* (seems not quite right)
instance [Add α] : VAdd (Vc α n) (Vc α n) where
  vadd v p := ⟨ v.1 + p.1 ⟩

-- SIMP ENABLED
-- @[simp]
theorem Vc.vadd_def [Add α] (v : Vc α n) (p : Vc α n) :
  v +ᵥ p = ⟨ v.1 + p.1 ⟩ := rfl
@@@ -/

/- @@@
#### Neg

No separate notation class.
@@@ -/

instance [Neg α] : Neg (Vc α n) where
   neg t := ⟨ -t.1 ⟩

theorem Vc.neg_def [Neg α] (t : Tuple α n) :
  -t = ⟨ -t.1 ⟩ := rfl


/- @@@
#### Sub
@@@ -/

instance [Sub α] : Sub (Vc α n) where
  sub t1 t2 := ⟨t1.1 - t2.1⟩

-- @[simp]
theorem Vc.sub_def [Sub α] (t1 t2 : Vc α n) :
  t1 - t2 = ⟨t1.1 - t2.1⟩ := rfl


/- @@@
#### HSub

This is the heterogeneous subtraction (-) otation-defining class
@@@ -/

instance [Sub α] : HSub (Vc α n) (Vc α n) (Vc α n) where
  hSub := Sub.sub

theorem Vc.hSub_def [Sub α] (v w : Vc α n) :
  HSub.hSub v w = ⟨ v.1 - w.1 ⟩ := rfl


/- @@@
#### SMul

SMul is its own notation class.
@@@ -/

instance [SMul α α] : SMul α (Vc α n) where
  smul a t := ⟨ a • t.1 ⟩

-- @[simp]
theorem Vc.smul_def [SMul α α] (a : α) (t : Vc α n) :
  a • t = ⟨ a • t.1 ⟩ := rfl


/- @@@
### Structures
@@@ -/

/- @@@
#### AddCommSemigroup
@@@ -/

instance [AddCommSemigroup α]: AddCommSemigroup (Vc α n) :=
{
  add_comm := by     -- So you can see the steps
    intros
    ext i
    apply add_comm
  add_assoc := by intros; ext; apply add_assoc
}


/- @@@
Had a bug here: included [Add α] as well as [Semigroup α]
thereby getting two equivalent but different definitions
of +. Try adding [Add α] to see how the problem manifests.
@@@ -/
instance [AddSemigroup α] : AddSemigroup (Vc α n) :=
{
  add := Add.add
  add_assoc := by
    intros a b c
    simp [Vc.add_def]
    apply add_assoc
}

/- @@@
#### AddCommMonoid
@@@ -/

instance [AddCommMonoid α] : AddCommMonoid (Vc α n) :=
{
  add := Add.add
  zero := Zero.zero
  nsmul := nsmulRec
  add_assoc := by intros; ext; apply add_assoc
  zero_add := by intros; ext; apply zero_add
  add_zero := by intros; ext; apply add_zero
  add_comm := by intros; ext; apply add_comm
}

/- @@@
#### Module α (Vc α n)
@@@ -/
instance [Semiring α] : Module α (Vc α n) :=
{
  smul_add := by intros a x y; ext i; apply mul_add,
  add_smul := by intros a b x; ext i; apply add_mul,
  mul_smul := by intros a b x; ext i; apply mul_assoc,
  one_smul := by intros x; ext i; apply one_mul,
  zero_smul := by intros x; ext i; apply zero_mul,
  smul_zero := by intros a; ext i; apply mul_zero
}

#synth (AddZeroClass ℚ)

instance [AddZeroClass α] : AddZeroClass (Vc α n) :=
{
  zero_add := by
    intros x
    ext i
    apply zero_add


  add_zero := by
    intros x;
    ext i;
    apply add_zero
}

instance [AddMonoid α] : AddMonoid (Vc α n) :=
{
  nsmul := nsmulRec

  zero_add := by
    intro a
    ext
    apply zero_add

  add_zero := by
    intro a
    ext
    apply add_zero
}

/- @@@
Same problem here. Had both [Add α] and [AddSemigroup α],
the latter of which extends [Add α].
@@@ -/
--#synth (SubNegMonoid ℚ)

/-
instance [SubNegMonoid α] : SubNegMonoid (Vc α n) :=
{
  zero_add := by
    intro a;
    ext
    apply zero_add

  add_zero := by
    intro a;
    ext
    apply add_zero

  sub_eq_add_neg := by
    intro a b
    ext
    apply sub_eq_add_neg

  nsmul := nsmulRec
  zsmul := zsmulRec
_
-/

instance [SubNegMonoid α] : SubNegMonoid (Vc α n) :=
{
  zsmul := zsmulRec
  sub_eq_add_neg := by intros a b; ext i; apply sub_eq_add_neg
}

instance [SubNegMonoid α] : SubNegMonoid (Vc α n) :=
{
  zero_add := by
    intro a;
    ext
    apply zero_add

  add_zero := by
    intro a;
    ext
    apply add_zero

  sub_eq_add_neg := by
    intro a b
    ext
    apply sub_eq_add_neg

  nsmul := nsmulRec
  zsmul := zsmulRec

}

instance [AddGroup α] : AddGroup (Vc α n) :=
{
  neg_add_cancel := by
    intro a
    ext
    apply neg_add_cancel
}


-- Yay
-- Now that we can have Vc as the type of p2 -ᵥ p1
-- with p1 p2 : Pt
-- We can have Torsor Vc Pt
-- And that is affine space for any Vc sastisfying and Pt satisfying
 end DMT1.Algebra.Vector
