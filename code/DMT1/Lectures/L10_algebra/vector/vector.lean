import Mathlib.Data.Rat.Defs
import DMT1.Lectures.L10_algebra.tuple.tuple

namespace DMT1.Algebra.Vector

universe u
variable
  {n : Nat}
  {α : Type u}

----------------------------------------------------
/- @@@
# Vectors: Vc α n

TODO: Update this explanation for loss of Tuple type
We now define our abstract vector type, *Vc α n*, in
the same way, but now using *Tuple α n* as a concrete
representation. We lift the operations and structures
we need from the underlying *Tuple* type, just as did
for *Tuple* from he underlying scalar *K* type.
@@@ -/

/- @@@
## Representation as Fin n → α
@@@ -/

@[ext]
structure Vc (α : Type u) (n : Nat) : Type u where
  (toRep : Fin n → α)
-- deriving Repr


/- @@@
### Special Values: Zero (Vc α n)
@@@ -/

instance [Zero α]: Zero (Vc α n) where
  zero := ⟨ 0 ⟩


@[simp]
theorem Vc.zero_def [Zero α] :
  (0 : Vc α n) = ⟨ ( 0 : Fin n → α) ⟩ := rfl


/- @@@
## Operations
@@@ -/



/- @@@
### Add (Vc α n)
@@@-/

instance [Add α] : Add (Vc α n) where
  add t1 t2 := ⟨ t1.1 + t2.1 ⟩

-- SIMP ENABLED HERE
theorem Vc.add_def [Add α] (t1 t2 : Vc α n) :
  t1 + t2 = ⟨ t1.1 + t2.1 ⟩ := rfl

theorem Vc.add_toRep [Add α] {n : ℕ} (x y : Vc α n) (i : Fin n) :
  (x + y).1 i = x.1 i + y.1 i := rfl




/- @@@
### HAdd (Vc α n) (Vc α n) (Vc α n)
@@@-/

-- Support for Vc `+` notation using HAdd
@[simp]
instance [Add α]  : HAdd (Vc α n) (Vc α n) (Vc α n) :=
{ hAdd := Add.add }

@[simp]
theorem Vc.hAdd_def [Add α] (v w : Vc α n) :
  v + w = ⟨ v.1 + w.1 ⟩ := rfl

theorem Vc.hAdd_toRep [Add α] {n : ℕ} (x y : Vc α n) (i : Fin n) :
  (x + y).1 i = x.1 i + y.1 i := rfl



/- @@@
### Neg (Vc α n)

No separate notation class.
@@@ -/

instance [Neg α] : Neg (Vc α n) where
   neg t := ⟨ -t.1 ⟩

-- TODO: Release note
theorem Vc.neg_def [Neg α] (t : Vc α n) :
  -t = ⟨ fun i => -(t.1 i) ⟩ := rfl

theorem Vc.neg_toRep [Neg α] {n : ℕ} (x : Vc α n) (i : Fin n) :
  -x.1 i = -(x.1 i) := rfl



/- @@@
### Sub (Vc α n)
@@@ -/

instance [Sub α] : Sub (Vc α n) where
  sub t1 t2 := ⟨t1.1 - t2.1⟩

-- @[simp]
theorem Vc.sub_def [Sub α] (t1 t2 : Vc α n) :
  t1 - t2 = ⟨t1.1 - t2.1⟩ := rfl

theorem Vc.sub_toRep [Sub α] {n : ℕ} (x y : Vc α n) (i : Fin n) :
  (x - y).1 i = x.1 i - y.1 i := rfl



/- @@@
### HSub (Vc α n) (Vc α n) (Vc α n)

This is the heterogeneous subtraction (-) otation-defining class
@@@ -/

instance [Sub α] : HSub (Vc α n) (Vc α n) (Vc α n) where
  hSub := Sub.sub

theorem Vc.hSub_def [Sub α] (v w : Vc α n) :
  HSub.hSub v w = ⟨ v.1 - w.1 ⟩ := rfl

@[simp]
theorem Vc.hSub_toRep [Sub α] (v w : Vc α n) (i : Fin n) :
  (v - w).1 i = v.1 i - w.1 i := rfl


/- @@@
### SMul α (Vc α n)
@@@ -/

instance [SMul α α] : SMul α (Vc α n) where
  smul a t := ⟨ a • t.1 ⟩

theorem Vc.smul_Vc_def [SMul α α] (a : α) (v : Vc α n) :
  a • v = ⟨ a • v.toRep ⟩ := rfl

theorem Vc.smul_Vc_toRep [SMul α α] (a : α) (v : Vc α n) (i : Fin n) :
  (a • v).toRep i = a • (v.toRep i) :=
rfl


/- @@@
### HSMul α vc vc
@@@ -/
instance [SMul α α] : HSMul α (Vc α n) (Vc α n) where
  hSMul := SMul.smul

theorem Vc.hSMul_def [SMul α α] (a : α) (v : Vc α n) :
  a • v = ⟨ fun i => a • (v.1 i) ⟩ := rfl

theorem Vc.hsmul_toRep [SMul α α] (a : α) (v : Vc α n) (i : Fin n) :
  (a • v).toRep i = a • (v.toRep i) := rfl


/- @@@
### Structures
@@@ -/

/- @@@
#### AddCommSemigroup  (Vc α n)
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
### AddSemigroup  (Vc α n)

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
#### AddCommMonoid (Vc α n)
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


/- @@@
#### AddMonoid (Vc α n)
@@@ -/

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
#### SubNegMonoid
@@@ -/
instance [SubNegMonoid α] : SubNegMonoid (Vc α n) :=
{
  zsmul := zsmulRec
  sub_eq_add_neg := by intros a b; ext i; apply sub_eq_add_neg
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
