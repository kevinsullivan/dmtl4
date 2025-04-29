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

/- @@@
### Examples
@@@ -/

def myAffineEquiv : (ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ) :=
  AffineEquiv.refl (ℝ × ℝ) (ℝ × ℝ)

#eval myAffineEquiv (2.0, 3.0) -- Output should be (2.0, 3.0)
#eval myAffineEquiv.symm (5.0, -1.0) -- Output should be (5.0, -1.0)

/- @@@
```lean
AffineEquiv :
  (k : Type u_1) →
  (P₁ : Type u_2) →
  (P₂ : Type u_3) →
  {V₁ : Type u_4} →
  {V₂ : Type u_5} →
  [inst : Ring k] →
  [inst_1 : AddCommGroup V₁] →
  [inst_2 : Module k V₁] →
  [inst_3 : AffineSpace V₁ P₁] →
  [inst_4 : AddCommGroup V₂] →
  [inst : Module k V₂] →
  [inst : AffineSpace V₂ P₂] →
  Type (max (max (max u_2 u_3) u_4) u_5)
```
@@@-/


/- @@@
We define the following equivalences:

    AffineEquiv.refl k P: the identity map as an AffineEquiv;

    e.symm: the inverse map of an AffineEquiv as an AffineEquiv;

    e.trans e': composition of two AffineEquivs; note that the order follows
    mathlib's CategoryTheory convention (apply e, then e'), not the convention
    used in function composition and compositions of bundled morphisms.

We equip AffineEquiv k P P with a Group structure with multiplication
corresponding to composition in AffineEquiv.group.
```
@@@ -/



def idAffineEquiv
  [Field α]
  [AddCommGroup (Vc α n)]
  [Module α (Vc α n)]
  [AffineSpace (Vc α n) (Pt α n)] :
  Pt α n ≃ᵃ[α] Pt α n :=
  AffineEquiv.refl (Pt α n) (Pt α n)



-- def foo
--   [Field α]
--   [AddCommGroup (Vc α n)]
--   [Module α (Vc α n)]
--   [AddTorsor (Vc α n) (Pt α n)] :
-- Pt α n ≃ᵃ[α] Pt α n :=
--   AffineEquiv.refl (Pt α n)
