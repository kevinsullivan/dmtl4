import Mathlib.Data.Rat.Defs
import Mathlib.LinearAlgebra.AffineSpace.Defs
import DMT1.Lectures.L10_algebra.point.point

namespace DMT1.Algebra.Torsor

open DMT1.Algebra.Vector
open DMT1.Algebra.Point
open DMT1.Algebra.Tuples

universe u
variable
  {n : Nat}
  {α : Type u}

instance [AddGroup α] [Nonempty (Pt α n)] : AddTorsor (Vc α n) (Pt α n) :=
{
  -- ∀ (p₁ p₂ : Pt α n), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
  vsub_vadd':= by
    intros p1 p2
    simp [Pt.hVAdd_def]

  -- vadd_vsub' : ∀ (g : Vc α n) (p : Pt α n), (g +ᵥ p) -ᵥ p = g
  vadd_vsub':= by
    intro v p
    simp [Pt.vsub_def]
}

end DMT1.Algebra.Torsor
