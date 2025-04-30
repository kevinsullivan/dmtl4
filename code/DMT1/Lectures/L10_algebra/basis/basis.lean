import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.AffineSpace.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.Group
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.Matrix.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Algebra.Module.LinearMap.Defs
import DMT1.Lectures.L10_algebra.torsor.torsor


/- @@@
PLEASE IGNORE THIS FILE. UNDER CONSTRUCTION.
@@@ -/

namespace DMT1.Lecture.Bases

open DMT1.Algebra.Vector
open DMT1.Algebra.Tuples
open DMT1.Algebra.Torsor

universe u
variable
  {n : Nat}
  {α : Type u}


/- @@@
Bases. Lean's linear algebra library has rich support for formal
reasoning. Unfortulately for our computational purposes, much of
it is noncomputable. We want foundationally verified computation.
For mathematical generality, that library's infinite-dimensional
vector spaces, based Finsupp functions, from finite index sets of
values of possibly infinite types (such as Nat), to indexed values.

So we'll just suck it up and see what we might build from scratch,
albeit informed by a some familarity with the *concepts* employed
in the linear algebra library's design.

The most interesting is that we impose coordinates on a space of
objects by establishing a bijection between objects, on one hand,
and coordinate tuples, on the other other.
@@@ --/


namespace AffBasis

/- @@@
## LinearEquivalence

```lean
M ≃ₗ [R] M₂ denotes the type of linear equivalences between M and M₂ over a plain linear map M →ₗ M₂.
A linear equivalence comprises transformations in each direction and proofs of linearity axioms.
```
@@@ -/

def equivVcTuple [AddCommGroup α] [Semiring α] [Module α α] : Vc α n ≃ₗ[α] Tuple α n where
  -- to and from coordinates relative to a std basis on this space (we normalize eagerly right now)
  toFun := fun v => v.toRep
  invFun := fun t => ⟨t⟩

  -- left_inv : Function.LeftInverse (fun t => { toRep := t }) fun v => v.toRep
  left_inv := by intro v;  cases v; rfl

  -- right_inv : Function.RightInverse (fun t => { toRep := t }) fun v => v.toRep
  right_inv := by intro t; rfl

  -- map_add' : ∀ (x y : Vc α n), (x + y).toRep = x.toRep + y.toRep
  map_add' := by intros v₁ v₂; cases v₁; cases v₂; rfl

  -- map_smul' : ∀ (m : α) (x : Vc α n), (m • x).toRep = (RingHom.id α) m • x.toRep
  map_smul' := by
    intros a v
    cases v
    simp [Vc.smul_def]
    sorry -- not def-eq, likely instsance conflict issue, later


-- definition theorems
theorem vcTuple.equiv_apply
  [AddCommGroup α] [Semiring α] [Module α α]
  (v : Vc α n) : equivVcTuple.toFun v = v.toRep := rfl

theorem vcTuple.equiv_symm_apply
 [AddCommGroup α] [Semiring α] [Module α α]
 (t : Tuple α n) : equivVcTuple.symm t = ⟨t⟩ := rfl

/- @@@
## Vectors
@@@ -/


-- TODO: Release note. Simplification.
-- Vectors, with constructor parameters (1, 0), (0, 1), and (0, 2)
-- def vc0 : Vc ℚ 2 := ⟨ ⟨ fun i => match i with | 0 => 1 | 1 => 0 ⟩ ⟩
-- def vc1 : Vc ℚ 2 := ⟨ ⟨ fun i => match i with | 0 => 0 | 1 => 1 ⟩ ⟩
-- def vc1': Vc ℚ 2 := ⟨ ⟨ fun i => match i with | 0 => 0 | 1 => 2 ⟩ ⟩

def vc0 : Vc ℚ 2 := ⟨ fun i => match i with | 0 => 1 | 1 => 0 ⟩
def vc1 : Vc ℚ 2 := ⟨ fun i => match i with | 0 => 0 | 1 => 1 ⟩
def vc1': Vc ℚ 2 := ⟨ fun i => match i with | 0 => 0 | 1 => 2 ⟩
-- Nicer


/- @@@
## MATRIX VcTuple c r
@@@ -/

def twoVc := fun (i : Fin 2) => match i with | 0 => vc0 | 1 => vc1'

#eval twoVc 0


def aMatrix : Matrix (Fin 2) (Fin 2) ℚ := fun i j => ((twoVc i).toRep) j

-- Mathlib types
#check LinearEquiv
#check LinearMap
/-
```lean
A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`. Elements of `LinearMap σ M M₂` (available under the notation
`M →ₛₗ[σ] M₂`) are bundled versions of such maps. For plain linear maps (i.e. for which
`σ = RingHom.id R`), the notation `M →ₗ[R] M₂` is available. An unbundled version of plain linear
maps is available with the predicate `IsLinearMap`, but it should be avoided most of the time.

structure LinearMap {R S : Type*} [Semiring R] [Semiring S] (σ : R →+* S) (M : Type*)
    (M₂ : Type*) [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] extends
    AddHom M M₂, MulActionHom σ M M₂
```
-/


/- @@@

A LinearMap satisfies:

- Additivity: f (x + y) = f x + f y
- Homogeneity: f (a • x) = a • (f x)


A simple version of a linear map from a module M₁ to a module M₂ rep. wrt stdBasis
@@@ -/

structure LinearFinMap (α : Type u) (n m : ℕ) (dom codom : Type v)
  [Semiring α]
  [AddCommMonoid dom]
  [AddCommMonoid codom]
  [Module α dom]
  [Module α codom]
  where
  toFun : dom → codom
  map_add' : ∀ (x y : dom), toFun (x + y) = toFun x + toFun y
  map_smul' : ∀ (a : α) (x : dom), toFun (a • x) = a • toFun x

#check LinearFinMap ℚ 2 2 (Fin 2 → ℚ) (Fin 2 → ℚ)
#check LinearFinMap ℚ 2 2 (Tuple ℚ 2) (Fin 2 → ℚ)
#check LinearFinMap ℚ 2 2 (Vc ℚ 2) (Tuple ℚ 2)
#check LinearFinMap ℚ 2 2 (Vc ℚ 2) (Tuple ℚ 2)

#check (Tuple ℚ 2)

def swapMap [Semiring ℚ] [Module ℚ (Vc ℚ 2)] : LinearFinMap ℚ 2 2 (Vc ℚ 2) (Vc ℚ 2) :=
{
  toFun := fun v =>
    ⟨ fun
      | 0 => v.toRep 1
      | 1 => v.toRep 0 ⟩

  map_add' := by
    intros x y
    simp [Vc.add_def]
    simp [HAdd.hAdd]
    simp [Add.add]
    funext i
    fin_cases i
    rfl
    rfl

  map_smul' := by
    intros a x
    simp [Vc.smul_def]
    simp [SMul.smul]
    simp [MulAction.mul_smul]
    funext i
    fin_cases i
    rfl
    rfl


    -- apply congrArg Vc.mk
    -- simp [Vc.smul_toRep]

    -- funext i
    -- fin_cases i
    -- simp [Pi.smul_apply]
    -- simp [Pi.smul_apply]
}


structure LinearFinMap' (α : Type u) (n m : ℕ) [Semiring α] where
  toFun : Tuple α n → Tuple α m
  map_add' : ∀ (x y : Tuple α n), toFun (x + y) = toFun x + toFun y
  map_smul' : ∀ (a : α) (x : Tuple α n), toFun (a • x) = a • (toFun x)


  -- mathlib: def Matrix (m n : Type*) (α : Type*) := m → n → α
  -- LinearFinMap: Finite-dimensional linear maps
structure LinearFinMap'' (α : Type u) (n m : ℕ)  (dom codom : Type u)
  [Semiring α]
  [AddCommMonoid dom]
  [AddCommMonoid codom]
  [Module α dom]
  [Module α codom]
  [Semiring α]
  where
  toMatrix : Matrix (Fin m) (Fin n) α
  toFun : Tuple α n → Tuple α m := fun v => ⟨toMatrix.mulVec v.toRep⟩
  map_add' : ∀ (x y : Tuple α n), toFun (x + y) = toFun x + toFun y :=
    by
      intros x y
      apply Tuple.ext
      intro i
      simp [toFun, mulVec, dotProduct]
      rw [Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp [mul_add]

  map_smul' : ∀ (a : α) (x : Tuple α n), toFun (a • x) = a • (toFun x) :=
    by
      intros a x
      apply Tuple.ext
      intro i
      simp [toFun, mulVec, dotProduct]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp [mul_assoc]

structure LinearFinMap''' (α : Type u) (n m : ℕ) (dom codom : Type u)[Semiring α] where
  toMatrix : Matrix (Fin m) (Fin n) α
  toFun : Tuple α n → Tuple α m :=
    fun v => ⟨toMatrix.mulVec v.toRep⟩
  map_add' : ∀ (x y : Tuple α n), toFun (x + y) = toFun x + toFun y :=
    by
      intros x y
      apply Tuple.ext
      intro i
      simp [toFun, mulVec, dotProduct]
      rw [Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp [mul_add]

  map_smul' : ∀ (a : α) (x : Tuple α n), toFun (a • x) = a • (toFun x) :=
    by
      intros a x
      apply Tuple.ext
      intro i
      simp [toFun, mulVec, dotProduct]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp [mul_assoc]

def idMatrix (n : ℕ) (α : Type u) [Semiring α] : Matrix (Fin n) (Fin n) α :=
  Matrix.diagonal (fun _ => 1)

-- nxn case only at the moment
def LinearFinMap.ofMatrix [CommSemiring α] (M : Matrix (Fin n) (Fin n) α) : (LinearFinMap'' α n n) where
  toMatrix := M
  toFun := fun v => ⟨M.mulVec v.toRep⟩

  map_add' := by
    intros x y
    ext i
    simp only [Matrix.mulVec, dotProduct]
    simp only [Tuple.add_def, Pi.add_apply]
    rw [Finset.sum_congr rfl (fun j _ => by simp only [mul_add]; rfl)]
    rw [Finset.sum_add_distrib]
    rfl

  map_smul' := by
    intros a x
    ext i
    simp only [Matrix.mulVec, dotProduct]
    -- Expand scalar multiplication on tuples
    simp only [Tuple.smul_def, Pi.smul_apply]
    simp [SMul.smul]
    -- Now inside sum: M i j * (a • x.toRep j) --> M i j * (a * x.toRep j)
    rw [Finset.sum_congr rfl (fun j _ => by rw [←mul_assoc])]
    rw [Finset.sum_congr rfl (fun j _ => by rw [mul_comm (M i j) a])]
    rw [Finset.sum_congr rfl (fun j _ => by rw [mul_assoc])]
    rw [← Finset.mul_sum]
    rfl

#check aMatrix
def aLinMap := LinearFinMap.ofMatrix aMatrix
#eval aLinMap.toFun ⟨ fun i => match i with | 0 => 2 | 1 => 3 ⟩


structure LinEquiv (α : Type u) (n : Nat) (M₁ M₂ : Type u)
  [Semiring α] [AddCommMonoid M₁] [AddCommMonoid M₂][Module α M₁] [Module α M₂] extends (LinMap α n n (Vc α n) (Tuple α n)) where
(toCoords : LinMap α n n)
(fromCoords : LinMap α n n)

-- /-!
-- ## Fin n → α and Vector α n Conversions
-- This file defines:

-- - `Vector.toFun` : converts `Vector α n → Fin n → α`
-- - `funToVector` : converts `Fin n → α → Vector α n`
-- - optional: coercion from `Vector α n` to `Fin n → α`
-- - simple examples
-- -/

-- namespace FinVec

-- -- Convert Vector α n → Fin n → α
-- def Vc.toFun {α : Type u} {n : ℕ} (v : Vector α n) : Fin n → α :=
--   fun i => v.get i

-- -- Optional: CoeFun instance for automatic coercion
-- instance {α : Type u} {n : ℕ} : CoeFun (Vector α n) (fun _ => Fin n → α) where
--   coe := Vc.toFun

-- -- Convert Fin n → α → Vector α n
-- def funToVector {α : Type u} {n : ℕ} (f : Fin n → α) : Vc α n :=
--   ⟨List.ofFn f, List.length_ofFn f⟩

-- -- Examples

-- -- Example 1: Vector to function
-- def v1 : Vc ℕ 3 := ![10, 20, 30]

-- #eval v1 0  -- 10
-- #eval v1 1  -- 20
-- #eval v1 2  -- 30

-- -- Example 2: Function to Vector
-- def f1 : Fin 3 → ℕ := fun
--   | 0 => 7
--   | 1 => 8
--   | 2 => 9

-- def v2 : Vector ℕ 3 := funToVector f1

-- #eval v2.toList  -- [7, 8, 9]

-- Example 3: Round trip
-- example (v : Vector ℚ 4) : funToVector (Vector.toFun v) = v := by
--   cases v
--   simp [Vector.toFun, funToVector, List.ofFn, List.get]
--   apply congrArg
--   apply List.ext
--   intro i
--   simp
--   rfl
-- end FinVec




/- @@@
## Basis
@@@ -/

structure Basis (α : Type u) (n : Nat) [AddCommGroup α] [Semiring α] [Module α α]  where
rep :
  Vc α n ≃ₗ[α] Tuple α n
/- @@@
You get a pair of functions, Vc to Tuple ("coordinates"), and Tuple ("coordinates") to Vc,
satisfying specific linearity constraints.
@@@ -/



/- @@@
## Linear Maps
We might avoid going down this path for a bit. What we need and now have are linear equivalences.

https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/LinearMap/Defs.html#LinearMap
@@@ -/
#check LinearEquiv.mk



#check (equivVcTuple vc0 : Tuple ℚ 2)
#eval equivVcTuple vc0          -- ([1, 0] : Tuple ℚ 2)
#eval equivVcTuple vc1          -- ([0, 1] : Tuple ℚ 2)
#check (equivVcTuple.toFun vc0 : Tuple ℚ 2)
#eval equivVcTuple.toFun vc0    -- [1, 0]
#eval equivVcTuple.toFun vc1
#eval let
  tc := equivVcTuple.toFun vc0
  equivVcTuple.toFun ⟨ tc ⟩
#check let
  tc := equivVcTuple.toFun vc0
  equivVcTuple.invFun (equivVcTuple.toFun ⟨ tc ⟩ )

--------

/-
````lean
https://leanprover-community.github.io/theories/linear_algebra.html
```
-/


def fullRank (v : Fin n → Vc ℚ n) : Bool :=
  let m : Matrix (Fin n) (Fin n) ℚ := fun i j => (v j).toRep.toRep i
  m.det ≠ 0

def linearEquivToMatrix [AddCommGroup α] [Semiring α] [Module α α] (e : Vc α n ≃ₗ[α] Tuple α n) : Matrix (Fin n) (Fin n) α :=
fun i j => (e ⟨⟨fun k => if k = j then 1 else 0⟩⟩).toRep i

#eval linearEquivToMatrix (@equivVcTuple 2 ℚ inferInstance inferInstance inferInstance)

variable {α : Type _} [CommRing α] [Module α α] [AddCommGroup α] [Semiring α] [Module α α]

structure Vc : Type u where
(rep : Tuple α n)
(basis : MyBasis α n )

def matrixToLinearMap {n : ℕ} (M : Matrix (Fin n) (Fin n) α) : (Fin n → α) →ₗ[α] (Fin n → α) :=
{ toFun := fun v => M.mulVec v,
  map_add' := by
    intros x y
    ext i
    unfold Matrix.mulVec
    sorry,
  map_smul' := by
    intros a x
    ext i
    unfold Matrix.mulVec
    sorry
}



/-
Upgrade Vc.mk to take a 1xn or nx1 α-Matrix along with a Basis
Upgrade LinearMap to take a nxn α-Matrix and a Basis
Upgrade LinearMap to take a n-Tuple of Vc
-/

structure LinMap  [AddCommGroup α] [AddCommGroup (Fin n → α)] [Semiring (Fin n)] [AddCommGroup (Fin n)] [Semiring α] [Module α α] (a : α) (r c : Nat) where
(coords : Matrix (Fin r) (Fin c) α)
(basis : MyBasis (Fin n) n)


def mBasis [AddCommGroup α] [Semiring α] [Module α α] :  MyBasis α n := ⟨ equivVcTuple ⟩
def newBasis [AddCommGroup α] [Semiring α] [Module α α] (vs : Tuple (Vc α n) n) : MyBasis α n :=
MyBasis.mk (_)


/-
→ₗ[ℚ] is the notation for the type of linear maps over ℚ between two modules.

It’s short for LinearMap ℚ M N where:

    ℚ is the base field (scalars),

    M is the domain,

    N is the codomain.
-/




/- @@@
## Why Won't LinearAlgebra Compute
@@@ -/
open Finsupp
#check (@Basis.mk)
def vs : Fin 2 →₀ Vc ℚ 2 :=
  Finsupp.mk
    (Finset.univ)
    (fun
      | 0 => e0
      | 1 => e1)
    (
      by
      intro i
      constructor
      -- → direction
      intro _
      match i with
      | 0 =>
        simp only []
        -- show e0 ≠ 0
        have h : e0 ≠ 0 := by
          -- insert your proof that e0 ≠ 0
          intro h; sorry
        exact h
      | 1 =>
        simp only []
        have h : e1 ≠ 0 := by
          -- insert your proof that e1 ≠ 0
          intro h; sorry
        exact h

      -- ← direction
      intro h
      -- since Finset.univ contains all elements, done
      exact Finset.mem_univ i)

axiom li : LinearIndependent ℚ vs
axiom sp : ⊤ ≤ Submodule.span ℚ (Set.range ⇑vs)

def myBasis := Basis.mk li sp

/- @@@
```lean
@Basis.mk : {ι : Type u_1} →
  {R : Type u_2} →                                -- scalar type implicit
    {M : Type u_3} →                              -- module type implicit
      [inst : Semiring R] →                       -- semiring instance
        [inst_1 : AddCommMonoid M] →
          [inst_2 : Module R M] →                 -- module instance
            {v : ι → M} →                         -- vectors implicit
            LinearIndependent R v →               -- explicit proof
            ⊤ ≤ Submodule.span R (Set.range v)    -- explicit proof
→ Basis ι R M
```
@@@ -/


end AffFrame

end DMT1.Lecture.Bases
