import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Finset.Card
import Init.Data.Repr
import Mathlib.LinearAlgebra.AffineSpace.Defs


/- @@@
<!-- toc -->

# Finitely Multi-Dimensional Affine Spaces

One dimensional affine spaces are nice for modeling physical phenomena
that, at least in idealized forms, proceeds linearly. Classical notions
of time can be like this.

Sometimes, though, one-dimensionality is limiting. We'd thus consider
generalizing from 1-D affine spaces to *n*-D affine spaces. In parrticular,
we might use a 2-D affine space to represent the geometry of the planar
floor on which an imaginary robot endeavors tireless to pick up dust and
debris. A robot that can only move back and forth on a line isn't so good
at finding all the crumbs.

## Overview

The main driver of change, starting from what we developed in the 1-D case
to our parameterized design, will be the need to change from representating
a 1-D point as a single rational number, to an n-D representation. For that,
we will choose n-long ordered sequences of rationals.

It's a good idea not to think of these rational values as coordinates. They
serve to distinguish one point in an affine space from any different point,
and to ensure that there are enough points so that all of the now familiar
affine space axioms can satisfied.

Concretely we have to construct instances of the now familiar affine space
related typeclasses, but for our new n-D representation instead of for the
current 1-D representation.
@@@ -/

/- @@@
## Finite Nat Index Sets: Fin n

In mathematics, tuple is a common name for an ordered sequence of values.
A tuple with *n* values is said to be an *n-tuple*. If the values in the
tuple are of some type, α, one could say it's an *α n-tuple* (e.g., a real
3-tuple).

There are several ways to represent tuples in Lean. For example, one could
represent the set of, say, natural number 3-tuples, as the type of lists of
natural numbers that can be pairs with proofs that their lengths are 3. In
Lean, this type is called Vector. The Vector type builder is parameterized
by both the elemennt type (a type) and the length of the sequence (a value
of type Nat). This type is a standard example of a dependent type.

Another approach, that we will adopt here, is to represent an α n-tuple as
a function from the finite set of n natural numbers ranging from 0 to n-1,
to α values.

Now the question is how to represent such a finite set of α values so that
its values can serve as arguments to that order-imposing indexing function.

Lean provides the *Fin n* type for this purpose. It's values are all of the
natural numbers from 0 to n-1. If you try to assign a larger natural number
to an identifier of this type, the value will be reduced mod n to a value
in the designated range of index values.
@@@ -/

#eval (0 : Fin 3)
#eval (1 : Fin 3)
#eval (2 : Fin 3)
#eval (3 : Fin 3)
#eval (4 : Fin 3)

/- @@@
## n-Tuple of α as Fin n → α

With this in mind, we can represent a rational 3-tuple, for example,
as a function, *t*, taking an index, i, of type Fin 3, and returning
*f i*. Using this scheme, we'd express the tuple t = (1/2, 1/3 ,1/6)
as the following function.
@@@ -/

def aRawTuple : Fin 3 → ℚ
| 0 => 1/2
| 1 => 1/3
| 2 => 1/6

/- @@@
One then expresses index lookups in tuples using function applicatio.
@@@ -/

#eval aRawTuple 0
#eval aRawTuple 1
#eval aRawTuple 2

/- @@@
A value of type Fin n is actually a structure with a value between 0
and n-1 and a proof that it is. When writing functions that take Fin n
arguments, using pattern matching, you can match on both arguments. One
are often interesting only in the value.
@@@ -/

/- @@@
## Abstracting to a Tuple α n Type

We'll wrap tuples represented by values of (Fin n → α) to a
new *Tuple* type, parametric in both α and *n*. With this type
in hand, we will then define a range of operations on tuples.

### Tuple Data Type
@@@ -/


structure Tuple (α : Type u) (n : ℕ) where
  toFun : Fin n → α

/- @@@
### Overloaded Operations
@@@ -/

-- For Lean to pretty print tuples, e.g., as #eval outputs
instance [Repr α] : Repr (Tuple α n) where
  reprPrec t _ := repr (List.ofFn t.toFun)

-- A coercion to extract the (Fin n → α) representation
instance : CoeFun (Tuple α n) (fun _ => Fin n → α) where
  coe := Tuple.toFun

-- Element-wise tuple addition; depends on coercion
instance [Add α] : Add (Tuple α n) where
  add x y := ⟨fun i => x i + y i⟩

-- Element-wise heterogeneous addition
instance [HAdd α β γ] : HAdd (Tuple α n) (Tuple β n) (Tuple γ n) :=
{ hAdd x y := ⟨fun i => x i + y i⟩ }

-- Element-wise multiplication
instance [Mul α] : Mul (Tuple α n) where
  mul x y := ⟨fun i => x i * y i⟩

-- Element-wise negation
instance [Neg α] : Neg (Tuple α n) where
  neg x := ⟨fun i => - x i⟩

-- Exercise: Overload Subtraction for this type

-- Pointwise scalar multiplication for tuples
instance [SMul R α] : SMul R (Tuple α n) where
  smul r x := ⟨ fun i => r • x i ⟩

instance [Zero α]: Zero (Tuple α n) := ⟨ ⟨ fun _ => 0 ⟩  ⟩


/- @@@
### Example
@@@ -/

-- Example
def myTuple : Tuple ℚ 3 :=
{ toFun := aRawTuple }

def v1 := myTuple
def v2 := 2 • v1
def v3 := v2 + 2 • v2
#eval v3


/- @@@
## Representing α n-Vectors as Tuples

We will now represent n-dimensional α *vectors* as
n-tuples of α values, represented in this manner.

### Vc Data Type
@@@ -/

structure Vc (α : Type u) (n: Nat) where
(tuple: Tuple α n)


/- @@@
### Overloaded Operations
@@@ -/

-- A coercion to extract the (Fin n → α) representation
instance : Coe (Vc α n) (Tuple α n) where
  coe := Vc.tuple

-- Element-wise heterogeneous addition; note Lean introducing types
instance [HAdd α β γ] : HAdd (Vc α n) (Vc β n) (Vc γ n) :=
{ hAdd x y := ⟨ x.tuple + y.tuple ⟩  }

-- Element-wise tuple addition; depends on coercion
instance [Add α] : Add (Vc α n) where
  add x y := ⟨ x.tuple + y.tuple ⟩

-- Element-wise multiplication
instance [Mul α] : Mul (Vc α n) where
  mul x y := ⟨ x.tuple * y.tuple ⟩

-- Element-wise negation
instance [Neg α] : Neg (Vc α n) where
  neg x := ⟨-x.tuple⟩

-- Pointwise scalar multiplication for tuples
instance [SMul R α] : SMul R (Vc α n) where
  smul r x := ⟨ r • x.tuple ⟩

/-
instance [Zero α]: Zero (Vc α n) :=
{
  zero := ⟨ Tuple.mk 0 ⟩
}
-/

/- @@@
### Example

Here's an example: the 3-D rational vector,
(1/2, 1/3, 1/6) represented as an instance of
the type, *NVc ℚ 3*.
@@@ -/

def a3ℚVc : (Vc ℚ 3) := ⟨ myTuple ⟩
#eval a3ℚVc + (1/2:ℚ) • a3ℚVc


/- @@@
### Representing Points as Tuples

We will now represent n-dimensional α *points* * as
n-tuples of α values, in turn represented with Fin n.

### Pt Data Type
@@@ -/

structure Pt (α : Type u) (n: Nat) where
(tuple: Tuple α n)


/- @@@
### Overloaded Operations
@@@ -/

-- A coercion to extract the (Fin n → α) representation
instance : Coe (Pt α n) (Tuple α n) where
  coe := Pt.tuple

/- @@@
HOMEWORK: Establish an affine space (AddTorsor) structure
on Vc and Pt.
@@@ -/

/- @@@
Here's an example: Let's make Vc into an additive monoid.
@@@ -/

instance (α : Type u) (n : Nat) : AddMonoid (Vc α n) :=
{
  add_assoc := _
  zero := _
  zero_add := _
  add_zero := _
  nsmul := _
}


instance (α : Type u) (n : Nat) : AddTorsor (Vc α n) (Pt α n) := _


/- @@@
Here's an example: Let's make Vc into an additive monoid.
@@@ -/

instance (α : Type u) (n : Nat) : AddMonoid (Vc α n) :=
{
  add := _
  add_assoc := _
  zero := _
  zero_add := _
  add_zero := _
  nsmul := _
}
