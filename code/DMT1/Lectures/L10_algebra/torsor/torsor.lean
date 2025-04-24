import Init.Data.Repr
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.AffineSpace.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.Group

import DMT1.Lectures.L10_algebra.point.point

namespace DMT1.Lecture.Torsor

open DMT1.Algebra.Vector
open DMT1.Algebra.Point

universe u
variable
  {n : Nat}
  {α : Type u}

/-
class AddTorsor
  (G : outParam Type*)
  (P : Type*)
  [AddGroup G]
    extends
  AddAction G P,
  VSub G P
    where
  [nonempty : Nonempty P]
  vsub_vadd' : ∀ p₁ p₂ : P, (p₁ -ᵥ p₂ : G) +ᵥ p₂ = p₁
  vadd_vsub' : ∀ (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
  -/

#check instAddGroupVc
#check instAddActionVcPt
#check instVSubVcPtOfSub

#synth AddAction (Vc ℚ 3) (Pt ℚ 3)
#synth AddGroup (Vc ℚ 3)
#synth VSub (Vc ℚ 3) (Pt ℚ 3)

#check AddTorsor.mk
/-
AddTorsor.mk.{u_1, u_2}
  {G : outParam (Type u_1)}
  {P : Type u_2}
  [AddGroup G]
  [toAddAction : AddAction G P]
  [toVSub : VSub G P]
  [nonempty : Nonempty P]
  (vsub_vadd' : ∀ (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁)
  (vadd_vsub' : ∀ (g : G) (p : P), (g +ᵥ p) -ᵥ p = g) :
  AddTorsor G P
-/


instance
  [AddGroup α]
  [Nonempty (Pt α n)]
  :

  AddTorsor (Vc α n) (Pt α n) :=
{
  vsub_vadd':= by
    --  ∀ (p₁ p₂ : Pt α n), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
    intros p1 p2
    simp only [Pt.vsub_vadd_def]
    apply congrArg Pt.mk
    _

  vadd_vsub':= by
    intro v p
    simp [Pt.vsub_def]
    _
}


/- @@@
Ack. Thank you: Rob_23oba.
@@@ -/
