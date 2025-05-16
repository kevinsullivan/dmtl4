import Mathlib.LinearAlgebra.AffineSpace.Defs
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import DMT1.Lectures.L10_algebra.torsor.torsor


import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

#check AffineEquiv.refl (ℝ × ℝ) (ℝ × ℝ)


open DMT1.Algebra.Torsor
open DMT1.Algebra.Point
open DMT1.Algebra.Vector

universe u
variable
  {n : Nat}
  {α : Type u}


/- @@@
# Affine Space

An *affine space* over a field *K* (here ℚ) is a
torsor (of points) *P* under a vector space *V* '
over (with scalars from) *K*.

Get *AffineSpace* (as a notation for *AddTorsor*)
by opening the Affine namespace.
@@@ -/

open Affine

#check (@AffineSpace)

instance
  [Field α]
  [AddCommGroup (Vc α n)]
  [Module α (Vc α n)]
  [AddTorsor (Vc α n) (Pt α n)] :
AffineSpace (Vc α n) (Pt α n) :=
{
  -- ∀ (p₁ p₂ : Pt α n), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
  -- ∀ (g : Vc α n) (p : Pt α n), (g +ᵥ p) -ᵥ p = g

  vsub_vadd' := by
    intros p1 p2
    simp [Pt.hVAdd_def]

  vadd_vsub':= by
    intro v p
    simp [Pt.vsub_def]
}

/- @@@
## Relation to Torsor in Lean 4

In Lean, AffineSpace is simply a notation for
Torsor. You can access this notation by opening
the Affine namespace, as shown here.
@@@ -/

#synth (AffineSpace (Vc ℚ 2) (Pt ℚ 2))

/- @@@
## New Concepts

Please see the Mathlib Affine Space [page](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/LinearAlgebra/AffineSpace/Defs.lean).

### AffineMap

A map between affine spaces that preserves the affine structure.

### AffineEquiv

An equivalence between affine spaces that preserves the affine structure;

### AffineSubspace

A subset of an affine space closed w.r.t. affine combinations of points;

### AffineCombination

An affine combination of points

### AffineIndependent

Affine independent set of points;

### AffineBasis.coord

The barycentric coordinate of a point.
@@@ -/

/- @@@
## Missing from Mathlib

Affine Frame
@@@ -/

/- @@@
## Affine Frame

Geometrically it's Point + Basis
@@@ -/

/- @@@
## Basis

Here's what it says in the Mathlib file.
```lean
Some key definitions are not yet present.

* Affine frames.  An affine frame might perhaps be represented as an `AffineEquiv` to a `Finsupp`
  (in the general case) or function type (in the finite-dimensional case) that gives the
  coordinates, with appropriate proofs of existence when `k` is a field.
```

Finsupp is off the table for us. We're about low-dimensional computation. So we'll use
AffineEquiv to a *coordinate-based tuple*, represented as a function: namely, Fin n → α.
Notably we are avoiding Finsupp, with a loss of generality from infinite dimensional (but
finitely supported) cases but with gains in computability and ease of proof construction.
@@@ -/

/- @@@
### AffineEquiv

See [this file](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/AffineSpace/AffineEquiv.html):

```lean
In this file we define AffineEquiv k P₁ P₂ (notation: P₁ ≃ᵃ[k] P₂) to be the type
of affine equivalences between P₁ and P₂, i.e., equivalences such that both forward
and inverse maps are affine maps.
@@@ -/

#check (@AffineEquiv)
