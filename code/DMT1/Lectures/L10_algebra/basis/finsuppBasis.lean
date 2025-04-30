import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.AffineSpace.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.Group
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.StdBasis

import DMT1.Lectures.L10_algebra.vector.vector

namespace DMT1.Lecture.Bases

open DMT1.Algebra.Vector

universe u
variable
  {n : Nat}
  {α : Type u}


#check Basis
/- @@@
```lean
Basis.{u_1, u_3, u_6} (ι : Type u_1)
  (R : Type u_3) (M : Type u_6)
  [Semiring R]
  [AddCommMonoid M]
  [Module R M] :
  Type (max (max u_1 u_3) u_6)
```
@@@ -/

#check Basis.mk
/- @@@
```lean
Basis.mk.{u_1, u_3, u_5}
  {ι : Type u_1}
  {R : Type u_3}
  {M : Type u_5}
  [Semiring R]
  [AddCommMonoid M]
  [Module R M]
  {v : ι → M}
  (hli : LinearIndependent R v)
  (hsp : ⊤ ≤ Submodule.span R (Set.range v)) :
Basis ι R M
```
@@@ -/


#check LinearEquiv
/- @@@
```lean
LinearEquiv.{u_12, u_13, u_14, u_15}
  {R : Type u_12}
  {S : Type u_13}
  [Semiring R]
  [Semiring S]
  (σ : R →+* S)
  {σ' : S →+* R}
  [RingHomInvPair σ σ']
  [RingHomInvPair σ' σ]
  (M : Type u_14)
  (M₂ : Type u_15)
  [AddCommMonoid M]
  [AddCommMonoid M₂]
  [Module R M]
  [Module S M₂] :
    Type (max u_14 u_15)
```
@@@ -/

#check Pi.basisFun
/- @@@
```lean
Pi.basisFun.{u_1, u_2}
  (R : Type u_1)
  (η : Type u_2)
  [Semiring R]
  [Finite η] :
Basis η R (η → R)
```
@@@ -/

------------------------------------------------


/- @@@
```lean
variable (ι R M)

A `Basis ι R M` for a module `M` is the type of `ι`-indexed `R`-bases of `M`.

The basis vectors are available as `DFunLike.coe (b : Basis ι R M) : ι → M`.
To turn a linear independent family of vectors spanning `M` into a basis, use `Basis.mk`.
They are internally represented as linear equivs `M ≃ₗ[R] (ι →₀ R)`,
available as `Basis.repr`.
@@@ -/

  `Basis.ofRepr` constructs a basis given an assignment of coordinates to each vector.
  ofRepr :: `repr` is the linear equivalence sending a vector `x` to its coordinates:
    the `c`s such that `x = ∑ i, c i`.
    repr : M ≃ₗ[R] ι →₀ R

```


-- Basis ι R M ↔ LinearEquiv R M (ι →₀ R)

```
PT

LinearMap: any linear function between modules over R.

LinearEquiv: a linear map that is a bijection (has an inverse).

Basis ι R M:

    Is defined via a LinearEquiv to ι →₀ R,

    Gives a coordinate system for M,

    The core method is repr : M ≃ₗ[R] ι →₀ R
```

@@@ -/



/- @@@
Plan

Basis.mk (α : Type u) (n : Nat): (rep : Fin n → BasisVector n) → (h : Linearly Independent b) → Basis

- sdf
- asdf
- fga


/- @@@
# Coordinates

Our geometric algebra is now complete and mercifully
coordinate-free! An abstract, coordinate-free algebra
(e.g., p₃ := (p₁ -ᵥ p₂) +ᵥ p₄) is a boon for clarity
of expression and formal engineering analysis.

But for computing (and more advanced geometry) nothing
beats coordinate systems. We aim to support arbitrary
coordinate systems on vector/linear, or affine, spaces
transformations between and two coordinate systems being
assuredly well typed and easily computable.

Let's just restrict our view for now to vector spaces.
We just succeded in constructing a vector space structure
around objects of type *Vc α n*. These objects do have
concrete numberical representations, but those are not
coordinates. Rather, coordinates are tuples of scalars
that give the weights on the associated basis vectors
needed to sum to the given vector.

We want to preclude normal operations, such as addition,
on coordinate tuples (or maybe even individual values)
whose individual scalar coordinate values is relative to
a specific *basis*. We will thus look at making the basis
part of the type of a coordinate tuple.

A basis in turn is understood as an Tuple α (Vc α n)
@@@ -/

def unitVector {α : Type u} {n : Nat} [Field α] (i : Fin n) := λ j => if j = i then (1:α) else 0

-- test for ℚ 3-space
#eval @unitVector ℚ 3 _ 0
#eval @unitVector ℚ 3 _ 1
#eval @unitVector ℚ 3 _

axiom linearIndep : (Fin n → Vec) → Prop

structure Basis [Field α] (α : Type u) (n : Nat) : Type u where
(vecs : Fin n → Vc α n)
(pf: linearIndep vecs)



end DMT1.Lecture.Bases
