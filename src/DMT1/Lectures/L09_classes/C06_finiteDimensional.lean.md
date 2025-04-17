```lean
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Finset.Card
import Init.Data.Repr
import Mathlib.LinearAlgebra.AffineSpace.Defs
```


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

## Finite Index Sets: Fin n

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

```lean
#eval (0 : Fin 3)
#eval (1 : Fin 3)
#eval (2 : Fin 3)
#eval (3 : Fin 3)
#eval (4 : Fin 3)
```

## Tuples: Fin n → α

We can represent an *α n-tuple* as a function, *t*, taking
an index, i, of type *Fin n*, and returning *t i*.

For example, we'd represent the tuple, *t = (1/2, 1/4, 1/6)*
as the following function.

```lean
def aFinTuple : Fin 3 → ℚ
| 0 => 1/2
| 1 => 1/4
| 2 => 1/6
```

One then expresses index lookups in tuples using function applicatio.

```lean
#eval aFinTuple 0
#eval aFinTuple 1
#eval aFinTuple 2
```

A value of type Fin n is actually a structure with two fields:
a value, and a proof it satisfies that it is between 0 and n-1
(expressed as *val < n*). When pattern matching on a value of
this type, match on both arguments. One if often interested in
just the value. The following example is a function that takes
a value of type *Fin n* and returns just the value part of it.

```lean
def getFinVal {n : Nat} : Fin n → Nat
| ⟨ val, _ ⟩ => val
#eval (getFinVal (7 : Fin 5)) -- Expect 7
```


### Overloads

```lean
-- For Lean to pretty print tuples, e.g., as #eval outputs
instance [Repr α] : Repr (Fin n → α) where
  reprPrec t _ := repr (List.ofFn t)

-- A coercion to extract the (Fin n → α) representation
-- Element-wise tuple addition; depends on coercion
instance [Add α] : Add (Fin n → α) where
  add x y := fun i => x i + y i

-- -- Element-wise heterogeneous addition
-- instance [HAdd α α α] : HAdd (Fin n → α) (Fin n → α) (Fin n → α) :=
-- { hAdd x y := fun i => x i + y i }

-- Element-wise multiplication
instance [Mul α] : Mul (Fin n → α) where
  mul x y := fun i => x i * y i

-- Element-wise negation
instance [Neg α] : Neg (Fin n → α) where
  neg x := fun i => - x i

-- TODO: Overload Subtraction for this type

-- Pointwise scalar multiplication for tuples
instance [SMul R α] : SMul R (Fin n → α) where
  smul r x := fun i => r • x i

instance [Zero α]: Zero (Fin n → α) := ⟨ fun _ => 0 ⟩
#check (0 : Fin 3 → Nat)
```


Now we turn to equality. We'll provide two definitions, the
first (Eq) logical, the second (BEq) computational returning
Bool. Here's the logical equality predicate.
```lean
def eqFinTuple {α : Type u} {n : Nat} (a b : Fin n → α) : Prop :=
  ∀ (i : Fin n), a i = b i
```

Here is an algorithm that actually *decides* equality, returning a
Boolean. Note that to decide whether two tuples, represented as
Fin n → α, are elementwise equal, requires that we can decide if
individual elements are equal. So this function also requires a
Boolean equality function on individual α values, provided by a
required implicit instance of the *BEq α* typeclass. Assuming that
there is an instance enables us to use *==* notation at the level
tuple of individual elements.
```lean
def eqFinTupleBool {α : Type u} {n : Nat} [BEq α] (a b : Fin n → α) : Bool :=
  (List.finRange n).all (λ i => a i == b i)
```

With that algorithm defined, we can now overload the *BEq*
operator for (Fin n → α) objects. Among other things, this
will give us the *==* notation for Boolean equality testing
on Fin-based tuples. A precondition for using this operator
is that the individual elements can be compared for equality
in the same way.
```lean
instance {α : Type} {n : Nat} [BEq α] : BEq (Fin n → α) :=
  { beq := eqFinTupleBool }
```


The DecidableEq typeclass overloads *=*. This is useful when
using *if (a = b) then ... else* in coding. The (a = b) would
ordinarily be a proposition but the result here will be Bool.
This typeclass also enables the *decide* tactic, which you can
use to determine the truth of equality propositions.
```lean
instance [DecidableEq α] : DecidableEq (Fin n → α) :=
  fun t1 t2 =>
    if h : ∀ i, t1 i = t2 i then
      isTrue (funext h)
    else
      isFalse (λ H => h (congrFun H))
```


### Examples

Now we can add, negate, subtract, and pointwise multiply
tuples, scale them using scalar multiplication, and decide
if two of them are equal, using all of the nice notations,
and other results, that come with the respective typeclasses.

```lean
#eval aFinTuple == aFinTuple        -- (from BEq) expect true
#eval aFinTuple = aFinTuple         -- (from DecidableEq) expext true
#eval aFinTuple == (2 • aFinTuple)  -- expect false
#eval aFinTuple = (2 • aFinTuple)   -- expect false
#eval aFinTuple * aFinTuple         -- pointwise *
```




## Tuples: Tuple α n

We'll wrap tuples represented by values of (Fin n → α) in  a
new *Tuple* type, parametric in *α* and *n*. With this type
in hand, we will then define a range of operations on tuples,
mostly by just *lifting* operations from the (Fin n → α) type.

Note! Having defined decidable equality and other typeclass
instances for *Fin n → α*, Lean can now automaticallysynthesize
the corresponding typeclasses instances for our Tuple type!

### Data Type

```lean
structure Tuple (α : Type u) (n : ℕ) where
  toFun : Fin n → α
deriving Repr, DecidableEq, BEq     -- Look here!
```


### Overloads

```lean
-- A coercion to extract the (Fin n → α) representation
-- instance : Coe (Tuple α n) (Fin n → α) where
--  coe t := t.toFun

instance : CoeFun (Tuple α n) (fun _ => Fin n → α) where
  coe t := t.toFun

-- -- Element-wise heterogeneous addition
-- instance [HAdd α α α] : HAdd (Tuple α n) (Tuple α n) (Tuple α n) :=
--   { hAdd x y := ⟨ x + y ⟩ }   -- the "+" is for *Fin n → α*

-- Element-wise tuple addition; depends on coercion
instance [Add α] : Add (Tuple α n) where
  add x y :=  ⟨ x + y ⟩


-- Element-wise multiplication
instance [Mul α] : Mul (Tuple α n) where
  mul x y := ⟨ x * y ⟩

-- Element-wise negation
instance [Neg α] : Neg (Tuple α n) where
  neg x := ⟨ -x ⟩

-- TODO (EXERCISE): Overload Subtraction for this type

-- Pointwise scalar multiplication for tuples
instance [SMul R α] : SMul R (Tuple α n) where
  smul r x := ⟨ r • x ⟩

instance [Zero α]: Zero (Tuple α n) :=
  { zero := ⟨ 0 ⟩ }
```

### Example

```lean
-- Example
def myTuple : Tuple ℚ 3 := ⟨ aFinTuple ⟩

def v1 := myTuple
def v2 := 2 • v1
def v3 := v2 + 2 • v2
#eval v1 == v1
#eval v1 == v2
```


## Vectors: Vc α n

We will now represent n-dimensional α *vectors* as
n-tuples of α values, represented as *Tuple* values.

### Data Type

```lean
structure Vc (α : Type u) (n: Nat) where
  (tuple: Tuple α n)
deriving Repr, DecidableEq, BEq
```


### Overloads

```lean
-- A coercion to extract the (Fin n → α) representation
instance : Coe (Vc α n) (Tuple α n) where
  coe := Vc.tuple

-- -- Element-wise heterogeneous addition; note Lean introducing types
-- instance [HAdd α α α] : HAdd (Vc α n) (Vc α n) (Vc α n)  :=
-- { hAdd x y := ⟨ x.tuple + y.tuple ⟩  }

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

instance [Zero α]: Zero (Vc α n) :=
  { zero := ⟨ 0 ⟩ }
```

### Example

Here's an example: the 3-D rational vector,
(1/2, 1/3, 1/6) represented as an instance of
the type, *NVc ℚ 3*.

```lean
def a3ℚVc : (Vc ℚ 3) := ⟨ myTuple ⟩
def b3ℚVc := a3ℚVc + (1/2:ℚ) • a3ℚVc
#eval a3ℚVc == a3ℚVc  -- == is from BEq
#eval a3ℚVc == b3ℚVc
#eval a3ℚVc = b3ℚVc   -- = is from DecidableEq
#eval a3ℚVc + b3ℚVc + b3ℚVc
```



## Points: Pt α n

We will now represent n-dimensional α *points* * as
n-tuples of α values in the same way.

### Data Type

```lean
structure Pt (α : Type u) (n: Nat) where
  (tuple: Tuple α n)
deriving Repr, DecidableEq, BEq
```

### Overloads

We're *not* going to lift operation such as addition
from Tuple to Pt because such operations won't make
sense given the meaning we intend Pt objects to have:
that they represent *points* in a space, which cannot
be added together.

```lean
-- A coercion to extract the (Fin n → α) representation
instance : Coe (Pt α n) (Tuple α n) where
  coe := Pt.tuple
```



## α Affine n-Spaces

TODO (EXERCISE): Build an affine space structure on Vc and Pt.

```lean
-- TODO: This is what to implement
-- instance (α : Type u) (n : Nat) : AddTorsor (Vc α n) (Pt α n) := _
```


### Starter Example

To give you a good start on the overall task, here's
a completed construction showing that our Vc vectors
form an additive monoid. We already have a definition
of *+*. We'll need a proof that *+* is associative, so
let's see that first.

```lean
theorem vcAddAssoc {α : Type u} {n : Nat} [Ring α]:
  ∀ (v1 v2 v3 : Vc α n), v1 + v2 + v3 = v1 + (v2 + v3) := by
  -- Assume three vectors
  intro v1 v2 v3
  -- strip Vc and Tuple abstraction
  apply congrArg Vc.mk
  apply congrArg Tuple.mk
```
  NB: We now must show equality of  underlying Fin n → α
  *functions*. For this we're going to need an axiom that
  is new to us: the axiom of *functional extensionality*.
  What it says is if two functions produce the same outputs
  for all inputs then they are equal (even if expressed in
  very different ways). Look carefully at the goal before
  and after running *funext*.
```lean
  apply funext
  -- Now prove values are equal for arbitrary index values
  intro i
  -- This step is not necessary but gives better clarity
  simp [HAdd.hAdd]
  -- Finally appeal to associativity of α addition
  apply add_assoc
```
  Go read the add_assoc theorem and puzzle through how
  its application here finishes the proof.

With that, we're two steps (*add* and *add_assoc*) closer
to showing that our n-Dimensional vectors form a Monoid (as
long as α itself has the necessary properties (e.g., that the
α + is associative). We ensure that by adding the precondition
that α be a Ring. That will ensure that α has all of the usual
arithmetic operations and proofs of properties.

```lean
instance (α : Type u) (n : Nat) [Ring α]: AddMonoid (Vc α n) :=
{
  -- add is already available from the Add Vc instance.

  add_assoc := vcAddAssoc   -- The proof we just constructed

  zero := 0                 -- The Vc zero vector

  zero_add := by            -- ∀ (a : Vc α n), 0 + a = a
    intro a
    apply congrArg Vc.mk
    apply congrArg Tuple.mk
    funext                  -- The tactic version
    simp [Add.add]
    rfl

  add_zero :=  by             -- ∀ (a : Vc α n), a + 0 = a
    intro a
    apply congrArg Vc.mk
    apply congrArg Tuple.mk
    funext
    simp [Add.add]
    rfl

  nsmul := nsmulRec
}
```

Yay. Vc forms an additive monoid.

### Your Job

TODO: Continue with the main task. A precondition for forming
an additive torsor is to show that Vc forms an additive group.
You might want to start with that!

```lean
instance {α : Type u} {n : Nat} [Ring α]: AddGroup (Vc α n) :=
{
}

instance {α : Type u} {n : Nat} [Ring α]: AddTorsor (Vc α n) (Pt α n) :=
{
}
```
