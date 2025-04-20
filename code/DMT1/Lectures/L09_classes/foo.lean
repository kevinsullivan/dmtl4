import Mathlib.Data.Finsupp.Basic
import Init.Data.Repr
import Mathlib.Data.Rat.Defs

import Mathlib.Data.Fin.Tuple.Basic

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.AffineSpace.Defs
import Mathlib.Algebra.Module.Pi

import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.List.ToFinsupp
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Fin     -- cons, tail, etc

import Mathlib.Algebra.Module.Basic


/- @@@
# Improved Design

We explored using →₀ α functions as tuple but eventually
concluded that Fin-based representations will be fine for
our purposes, which genereally invoving computing at lower
dimensions, anyway. For AI or other sparse high-dimensional
applications, →₀ might well be better.

The main addition of this chapter, then, is not a different,
better for some purposes, concrete implementation for a Tuple
type, but rather a better factored design, based on the fact
that Lean already provides generalized proofs that many types
of algebraic structures can be imposed on functions of type,
*Fin n → α*.

When we take values of this type to represent *α n-tuples*
by wrapping them in objects of a new type, Tuple α n, we can
use all the machinery provided by structures on the raw data
to define corresponding structures on these isomorphic types.

### Structures on ℚ
@@@ -/

#check inferInstanceAs (Add ℚ)
#check inferInstanceAs (Neg ℚ)
#check inferInstanceAs (Sub ℚ)
#check inferInstanceAs (Inv ℚ)
#check inferInstanceAs (Div ℚ)

-- additive structures
#check inferInstanceAs (AddMonoid ℚ)
#check inferInstanceAs (AddGroup ℚ)
#check inferInstanceAs (AddCommGroup ℚ)
#check inferInstanceAs (Module ℚ ℚ)
#check inferInstanceAs (Field ℚ)

-- affine structure
#check inferInstanceAs (AddTorsor ℚ ℚ)

-- multiplicative structures
#check inferInstanceAs (Monoid ℚ)
#check inferInstanceAs (CommMonoid ℚ)
#check inferInstanceAs (Semiring ℚ)
#check inferInstanceAs (CommSemiring ℚ)
#check inferInstanceAs (Ring ℚ)
#check inferInstanceAs (CommRing ℚ)
-- #check inferInstanceAs (Group ℚ)     -- nope
-- #check inferInstanceAs (CommGroup ℚ) -- nope


/- @@@
## Structures on Fin n → α
@@@ -/

#check inferInstanceAs (Add (Fin 3 → ℚ))
#check inferInstanceAs (HAdd (Fin 3 → ℚ) (Fin 3 → ℚ) (Fin 3 → ℚ))
#check inferInstanceAs (Neg (Fin 3 → ℚ))
#check inferInstanceAs (Sub (Fin 3 → ℚ))
#check inferInstanceAs (Inv (Fin 3 → ℚ))
#check inferInstanceAs (Div (Fin 3 → ℚ))

-- additive structures
#check inferInstanceAs (AddMonoid (Fin 3 → ℚ))
#check inferInstanceAs (AddGroup (Fin 3 → ℚ))
#check inferInstanceAs (AddCommMonoid (Fin 3 → ℚ))
#check inferInstanceAs (AddCommGroup (Fin 3 → ℚ))
#check inferInstanceAs (Module (Fin 3 → ℚ) (Fin 3 → ℚ))
-- #check inferInstanceAs (Field (Fin 3 → ℚ))   -- nope

-- affine structure
#check inferInstanceAs (AddTorsor (Fin 3 → ℚ) (Fin 3 → ℚ))

-- multiplicative structures
#check inferInstanceAs (Monoid (Fin 3 → ℚ))
#check inferInstanceAs (CommMonoid (Fin 3 → ℚ))
#check inferInstanceAs (Semiring (Fin 3 → ℚ))
#check inferInstanceAs (CommSemiring (Fin 3 → ℚ))
#check inferInstanceAs (Ring (Fin 3 → ℚ))
#check inferInstanceAs (CommRing (Fin 3 → ℚ))

-- #check inferInstanceAs (Group ℚ)     -- nope
-- #check inferInstanceAs (CommGroup ℚ) -- nope


/- @@@
## Diversion: Tuple Rep as Finsupp: ℕ →₀ ℚ
@@@ -/
-- defined structures on Finsupp-based tuples
#check inferInstanceAs (HAdd (ℕ →₀ ℚ) (ℕ →₀ ℚ) (ℕ →₀ ℚ))
#check inferInstanceAs (AddMonoid (ℕ →₀ ℚ))
#check inferInstanceAs (AddGroup (ℕ →₀ ℚ))
#check inferInstanceAs (AddCommGroup (ℕ →₀ ℚ))
#check inferInstanceAs (Semiring ℚ)
-- #check inferInstanceAs (Ring (ℕ →₀ ℚ)) -- nope

/- @@@
Here we use *inferInstance* (vs. *inferInstanceAs*) to
have Lean find an instance of the specified typeclass. We
can then access its fields, as it is an ordinary structure.
@@@ -/

def ℚ3ℚasModule : (Module ℚ (Fin 3 → ℚ)) := inferInstance
#check ℚ3ℚasModule.zero_smul

variable
  {α : Type u}
  {n : Nat}

---------------
/- @@@
## Tuple α n
@@@ -/
---------------


/- @@@
### Data

Wrap concrete tuple rep in polymorphic fixed-dimension Tuple type
@@@ -/
@[ext]
structure Tuple (α : Type u) (n : Nat) where
  toFin : Fin n →  α


/- @@@
### Overloads

To overload these essential operations and
structures for our new tuple type, will will
have to write typeclass instance definitions
for this type. Each will typically strip the
outer abstractions and satisfy the goal using
the underlying representation.
@@@-/

-- Coerce a Tuple back to its underlying rep type
instance :
  CoeFun (Tuple α n) (fun _ => (Fin n) → α) :=
    { coe v := v.toFin }

-- For Lean to pretty print such tuples, e.g., for #eval
instance [Repr α] : Repr (Fin n → α) where
  reprPrec t _ := repr (List.ofFn t)


-- How to promote operation
instance [Add α] : Add (Tuple α n) where
  --add t1 t2 := ⟨ t1.toFin + t2.toFin ⟩
  add t1 t2 := ⟨ t1 + t2 ⟩

instance [Neg α] : Neg (Tuple α n) where
   neg t := ⟨ -t.toFin ⟩
  --neg t := ⟨ fun i => -(t i) ⟩

instance [Add α] [Sub α] : Sub (Tuple α n) where
 sub t v := ⟨ fun i => t i - v i ⟩

instance [Zero α]: Zero (Tuple α n) :=
{
  zero := ⟨ fun (_ : Fin n) => 0 ⟩
}

instance [SMul α α] : SMul α (Tuple α n) :=
  { smul a t := ⟨ a • t.toFin ⟩ }
--    { smul a t := ⟨fun i => a • t i⟩ }




-- QUESTION
--instance [SMul α (Fin n → α)] : SMul α (Tuple α n) where
--  smul a v := ⟨ a • v.toFin ⟩   -- have to be explicit

instance [AddCommSemigroup α]: AddCommSemigroup (Tuple α n) :=
{
  add_comm := by     -- So you can see the steps
    intros
    ext i
    apply add_comm
  add_assoc := by intros; ext; apply add_assoc
}

instance [AddCommMonoid α] : AddCommMonoid (Tuple α n) :=
{
  add := Add.add
  zero := Zero.zero
  nsmul := nsmulRec

  add_assoc := by     -- So you can see the steps
    intros
    ext i
    apply add_assoc

  zero_add := by intros; ext; apply zero_add
  add_zero := by intros; ext; apply add_zero
  add_comm := by intros; ext; apply add_comm
}

instance [Semiring α] : Module α (Tuple α n) :=
{
  --smul := fun a x => ⟨fun i => a * x i⟩,
  smul_add := by intros a x y; ext i; apply mul_add,
  add_smul := by intros a b x; ext i; apply add_mul,
  mul_smul := by intros a b x; ext i; apply mul_assoc,
  one_smul := by intros x; ext i; apply one_mul,
  zero_smul := by intros x; ext i; apply zero_mul,
  smul_zero := by intros a; ext i; apply mul_zero
}

/- @@@ @@@@@@@@@@@
## Vector: Vc α n
@@@ @@@@@@@@@@@@-/

structure Vc (α : Type u) (n : Nat) : Type u where
  (toTuple : Tuple α n)

  -- Coerce a Tuple back to its underlying rep type
instance :
  CoeFun (Vc α n) (fun _ => Tuple α n) :=
    { coe v := v.toTuple }

-- How to promote operation
instance [Add α] : Add (Vc α n) where
  add := fun t1 t2 => ⟨t1 + t2⟩

-- Zero tuple built from and just repeats zero α
instance [Zero α] : Zero (Vc α n) where
  zero := ⟨ 0 ⟩



instance {α : Type u} {m : Nat} [AddCommGroup α] :
  AddCommGroup (Vc α n) :=
{
  add t v := ⟨ t + v ⟩

  add_assoc := by
    intro a b c
    apply congrArg Vc.mk
    apply add_assoc -- (inferInstance : Fin n → ∀).add_assoc

  zero := ⟨ 0 ⟩

  zero_add := by
    intro a
    apply congrArg Vc.mk
    apply zero_add  -- (inferInstance : Fin n → ∀).zero_add

  add_zero := by
    intro a
    apply congrArg Vc.mk
    apply add_zero  -- (inferInstance : Fin n → ∀).add_zero

  nsmul := nsmulRec
}

/- @@@
### Examples
@@@ -/


def aFinTuple : Fin 3 → ℚ
| 0 => 1/2
| 1 => 1/4
| 2 => 1/6

def sum := aFinTuple + aFinTuple
def t31 : Tuple ℚ 3 := ⟨ aFinTuple ⟩
def t32 : Tuple ℚ 3 := 2 • t31
#reduce (t31 + t32).toFin 0   -- should be 1
#reduce (t31 + t32).toFin 1   -- should be 2
def v1 : Vc ℚ 3 := ⟨⟨ sum ⟩⟩  -- from Fin n → ℚ
def v2 : Vc ℚ 3 := ⟨ t32 ⟩    -- from Tuple α n

end tuple
