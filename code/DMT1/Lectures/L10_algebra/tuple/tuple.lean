import Mathlib.Data.Rat.Defs
import DMT1.Lectures.L10_algebra.scalar.scalar

namespace DMT1.Algebra.Tuples

open DMT1.Algebra.Scalar

universe u
variable
  {n : Nat}
  {α : Type u}


/- @@@
# Tuple Representation: Fin n → α

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

/- @@@
### HSMul α (Fin n → α)

One structure on Fin n → α that we'll need is scalar
multiplication, with notation, of an α-valued scalar
by a Fin n → α tuple. You can see that Lean does not
provide an instance by uncommenting #synth.
@@@ -/

-- #synth (HSMul ℚ (Fin _ → ℚ))
-- We must instantiate it for this application

instance [SMul α α]: HSMul α (Fin n → α) (Fin n → α) :=
{
  hSMul a f := SMul.smul a f
}

theorem hSMul_fin_def [SMul α α] (a : α) (f : Fin n → α) :
  a • f = fun i => a • (f i) := rfl

theorem hSMul_fin_toRep [SMul α α] (a : α) (f : Fin n → α) (i : Fin n) :
  (a • f) i = a • (f i) := rfl


end DMT1.Algebra.Tuples
