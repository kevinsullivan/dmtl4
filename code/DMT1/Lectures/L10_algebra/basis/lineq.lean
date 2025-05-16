import Mathlib.Data.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Field.Basic

open Matrix

-- Define the field and index type
variable {R : Type*} [Field R]
variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

-- The type of 2 x 2 matrix over R
#check Matrix (Fin n) (Fin n) R

-- Define a specific 2×2 matrix over ℚ
def M : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1, 2;
     3, 4]

-- You can check this if you like:
#eval M.det  -- Should evaluate to -2

-- Prove the determinant is a unit in ℚ
lemma det_M_is_unit : IsUnit M.det := by
  -- M.det = 1*4 - 2*3 = 4 - 6 = -2 ≠ 0 → it's a unit in ℚ
  unfold M
  norm_num

#eval Matrix.toLinearEquiv M det_M_is_unit

/- @@@
```lean
noncomputable def Matrix.toLinearEquiv
  {n : Type u_1}
  [Fintype n]
  {R : Type u_2}
  {M : Type u_3}
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  (b : Basis n R M)
  [DecidableEq n]
  (A : Matrix n n R)
  (hA : IsUnit A.det) :
M ≃ₗ[R] M

Given hA : IsUnit A.det and b : Basis R b, A.toLinearEquiv b hA is the LinearEquiv arising from toLin b b A.

See Matrix.toLinearEquiv' for this result on n → R.
```
@@@ -/
  noncomputable def Matrix.toLinearEquiv {n : Type u_1} [Fintype n] {R : Type u_2} {M : Type u_3} [CommRing R] [AddCommGroup M] [Module R M] (b : Basis n R M) [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) :
M ≃ₗ[R] M

-- Given hA : IsUnit A.det and b : Basis R b, A.toLinearEquiv b hA is the LinearEquiv arising from toLin b b A.

See Matrix.toLinearEquiv' for this result on n → R.

noncomputable def linEquivFromMatrix : (Fin 2 → ℚ) ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  Mathlib.LinearAlgebra.Matrix.ToLinearEquiv.toLinearEquiv M det_M_is_unit
