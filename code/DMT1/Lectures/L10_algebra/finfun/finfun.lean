import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.AffineSpace.Defs
import Mathlib.Algebra.Module.Pi

import DMT1.Lectures.L10_algebra.scalar.scalar

namespace DMT1.Algebra.Scalar

universe u
variable
  {n : Nat}
  {α : Type u}

/- @@@
# Fin n → α

A sequence is given its ordering by a function from ordered
indices to the values needing order. We will repersent finite
ordered α n-tuples as functions from {0, ..., n-1} index sets
to α values.
@@@ -/

/-@@@
## Pretty printing
@@@ -/

instance [Repr α] : Repr (Fin n → α) where
  reprPrec t _ := repr (List.ofFn t)

/- @@@-
## Structures on Fin n → α

Many algebraic structures on *Fin n → α* are already defined
in Lean's libraries. Here are just a few examples. A *zero* is
defined and has notation, 0.
@@@ -/

#synth (Zero (Fin _ → ℚ))
#synth (Add (Fin _ → ℚ))
#synth (AddCommGroup (Fin _ → ℚ))

end DMT1.Algebra.Scalar
