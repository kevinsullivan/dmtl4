import Init.Data.Repr
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.AffineSpace.Defs
import Mathlib.Algebra.Module.Pi

universe u
variable
  {n : Nat}
  {α : Type u}

namespace DMT1.Algebra.Scalar

/- @@@
# Scalars

Our intent is to support α affine n-spaces for dependable
computation. We will typecheck away errors made possible by
endemic widening of types by programmers for their earliest
years.

Because our intended abstraction, α affine n-spaces, which
involving α linear n-spaces (modules) as well, we require any
scalar type to come with the necessary structures defined and
with Lean able to synthesize instances as needed. Here we list
the structures that we build upon, using ℚ as a concrete scalar
value type

@@@ -/

end DMT1.Algebra.Scalar
