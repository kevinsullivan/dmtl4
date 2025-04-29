import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Module.Basic

universe u
variable
  {n : Nat}
  {α : Type u}

namespace DMT1.Algebra.Scalar

/- @@@
# Scalars
@@@ -/

/- @@@
### SMul α α

For this entire system we'll assume scalar
multiplication of a scalar by another scalar
is just ordinary multiplication.
@@@ -/

#synth (SMul ℚ ℚ)
#synth (SMul ℚ (Fin _ → ℚ))

instance [Mul α] : SMul α α := { smul := Mul.mul }

theorem Vc.smul_α_def [Mul α] (a b : α) :
  a • b =  a * b := rfl

theorem Vc.smul_α_toRep [Mul α] (a b : α) :
  a • b =  a * b := rfl


end DMT1.Algebra.Scalar
