import Init.Data.Repr
import Mathlib.Data.Rat.Defs

import Mathlib.Data.Fin.Tuple.Basic

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.AffineSpace.Defs
import Mathlib.Algebra.Module.Pi

import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Fin     -- cons, tail, etc

import Mathlib.Algebra.Module.Basic


/- @@@
# Improved Design

We explored using →₀ α functions as tuple but eventually
concluded that Fin-based representations will be fine for
our purposes, which genereally invoving computing at lower
dimensions, anyway. For AI or other sparse high-dimensional
applications, →₀ might well be better.

The main addition of this chapter, then, is not a different,
better for some purposes, concrete implementation for a Tuple
type, but rather a better factored design, based on the fact
that Lean already provides generalized proofs that many types
of algebraic structures can be imposed on functions of type,
*Fin n → α*.

When we take values of this type to represent *α n-tuples*
by wrapping them in objects of a new type, Tuple α n, we can
use all the machinery provided by structures on the raw data
to define corresponding structures on these isomorphic types.
@@@ -/




/- @@@
### Scalar K
@@@ -/

abbrev K := ℚ -- scalar type
def dim := 3  -- a default for now

/- @@@
#### K Operations
@@@ -/

#synth (Add K)
#synth (Neg K)
#synth (Sub K)
#synth (Inv K)
#synth (Div K)

/- @@@
#### K Additive Structures on K
@@@ -/

#synth (AddMonoid K)
#synth (AddGroup K)
#synth (AddCommGroup K)
#synth (Semigroup K)
#synth (Module K K)
#synth (Field K)


/- @@@
#### K Affine Structure on K
@@@ -/
#synth (AddTorsor K K)


/- @@@
#### K Multiplicative Structure on K
@@@ -/

#synth (Monoid K)
#synth (CommMonoid K)
#synth (Semiring K)
#synth (CommSemiring K)
#synth (Ring K)
#synth (CommRing K)

-- #synth (Group K)     -- nope
-- #synth (CommGroup K) -- nope


/- @@@
## α n-tuples

We will use Fin n → α to represent tuples.
@@@ -/


/- @@@
###  Fin n → α Operations
@@@ -/

#synth (Add (Fin dim → K))  -- define first, actual maths
#synth (HAdd (Fin dim → K) (Fin dim → K) (Fin dim → K))
#synth (Neg (Fin dim → K))
#synth (Sub (Fin dim → K))
#synth (Inv (Fin dim → K))
#synth (Div (Fin dim → K))
-- needed for additive torsor
#synth (VSub (Fin dim → K) (Fin dim → K))
#synth (HSub (Fin dim → K) (Fin dim → K) (Fin dim → K))

/- @@@
###  Fin n → α Structures

Lean has already established many structures on this type:
additive, affine, multiplicative.
@@@ -/

-- additive
#synth (AddMonoid (Fin dim → K))
#synth (AddGroup (Fin dim → K))
#synth (AddCommMonoid (Fin dim → K))
#synth (AddCommGroup (Fin dim → K))
#synth (Module (Fin dim → K) (Fin dim → K))
-- #synth (Field (Fin n → K))   -- nope

-- affine
#synth (AddTorsor (Fin dim → K) (Fin dim → K))

-- multiplicative
#synth (Monoid (Fin dim → K))
#synth (CommMonoid (Fin dim → K))
#synth (Semiring (Fin dim → K))
#synth (CommSemiring (Fin dim → K))
#synth (Ring (Fin dim → K))
#synth (CommRing (Fin dim → K))

-- not valid
-- #synth (Group K)     -- nope
-- #synth (CommGroup K) -- nope

-- Pretty printing (ignore details)
instance [Repr α] : Repr (Fin n → α) where
  reprPrec t _ := repr (List.ofFn t)


#eval inferInstanceAs (Zero (Fin dim → K))


-- zero := ⟨ fun (_ : Fin n) => 0 ⟩
-- TESTS
def aFinTuple : Fin 3 → ℚ := fun i => match i with | 0 => 1/2 | 1 => 1/4 | 2 => 1/6
#eval aFinTuple + aFinTuple   -- expect 1, 1/2, 1/3



/- @@@
## Implicit Declarations

Throughout the rest of this file, let α represent any type and
*n* any natural number dimension of a space.
@@@ -/
variable
  {α : Type u}
  {n : Nat}


---------------
/- @@@
## Tuples: Tuple α n

We'll now abstract *(Fin n → K)* as a type called *Tuple*, after
which we'll defined vectors and points as being represented by such
*Tuple* values. As *Tuple* is a new type, we will need to define
typeclass instances for it for all the operations and structures
we need on *Tuple* values. It's tedious, but there's a trick we'll
use repeatedly: strip the type abstractions, which add no content
in our design, and define operations and proofs for the new type
using the definitions of operations and proofs already available
for the underlying concrete representation type, *Fin n → K*.
@@@ -/


@[ext]
structure Tuple (α : Type u) (n : Nat) where
  toRep : Fin n →  α
deriving Repr, DecidableEq--, BEq

/- @@@
### Operations

We have to write typeclass instance definitions
for this type. Each will strip its type abstraction
and define operations using underlying representation.
@@@-/

/- @@@
Now we remove auto-coercion to rep, as harmful
to the enforcement of distinct abstractions over
common representation types.

```lean
-- Auto coerce to representation as function
instance :
  CoeFun (Tuple α n) (fun _ => (Fin n → α)) :=
    { coe v := v.toRep }

-- Pretty printing (ignore details)
instance [Repr α] : Repr (Tuple α n) where
  reprPrec t _ := repr (List.ofFn t)
```
@@@ -/
-- Pretty printing (ignore details)
instance [Repr α] : Repr (Tuple α n) where
  reprPrec t _ := repr (List.ofFn t.1)

/- @@@
Here's a key example: we define add on tuples
as Tuple.mk applied to the sum of the underlying
*(Fin n → K)* representations. The coercion is
being applied automatically to *t1* and *t2* on
the right hand side of the definition, as inside
the Tuple.mk notation, ⟨_⟩, a *(Fin n → K)* value
is expected. The *+* thus resolves to addition
for *Fin n → K* and the operands are expected to
be *(Fin n → K)* values. The coercion takes are
of pulling these representations out of *t1* and
*t2* to be combined into a representation for
the resulting sum *Tuple*. This pattern repeats
throughout this file.
@@@ -/

-- actual math
instance [Add α] : Add (Tuple α n) where
  add t1 t2 := ⟨ t1.1 + t2.1 ⟩

-- -- notations
-- instance [Add α] : HAdd (Tuple α n) (Tuple α n) (Tuple α n) :=
--   { hAdd := Add.add }

instance [Neg α] : Neg (Tuple α n) where
   neg t := ⟨ -t.1 ⟩

-- TODO: Not t and v are still tuple
instance [Sub α] : Sub (Tuple α n) where
 sub t v := ⟨ t.1 - v.1 ⟩

-- Needed eventually for torsor subtraction to vector
-- instance [Sub α] : HSub (Tuple α n) (Tuple α n) (Tuple α n) where
--   hSub t v := ⟨ t - v ⟩

 instance [Add α] [Sub α] : VSub (Tuple α n) (Tuple α n) :=
 { vsub := Sub.sub }

instance [Zero α] : Zero (Tuple α n) where
  zero := ⟨ 0 ⟩

-- TODO: Keep • or change to *? Why need coercion
instance [SMul α α] : SMul α (Tuple α n) where
  smul a t := ⟨ a • (t.1 : Fin n → α) ⟩

/- @@@
### Structures
@@@ -/

/- @@@
#### AddCommSemigroup
@@@ -/

instance [AddCommSemigroup α] : AddCommSemigroup (Tuple α n) :=
{
/- @@@
Here's a key example of lifing *proofs* from the
level of concrete representation to the level of
*Tuple* objects. We strip the *Tuple* abstraction
using the extensionality axiom for *Tuple* then
apply the corresponding theorem from the level of
the concrete representation. The *ext* tactic is
enabled by the *@[ext]* annotation we've attached
to the *Tuple* type definition. Use *ext* instead
of *apply congrArg Tuple.mk*. Now you know what it
actually does.
@@@ -/
  add_comm := by     -- So you can see the steps
    intros
    ext
    apply add_comm

  -- We can write such tactic scripts as one-liners
  add_assoc := by intros; ext; apply add_assoc
}

/- @@@
#### AddCommMonoid
@@@ -/

instance [AddCommMonoid α] : AddCommMonoid (Tuple α n) :=
{
  add := Add.add
  zero := Zero.zero
  nsmul := nsmulRec
  add_assoc := by intros; ext; apply add_assoc
  zero_add := by intros; ext; apply zero_add
  add_zero := by intros; ext; apply add_zero
  add_comm := by intros; ext; apply add_comm
}

/- @@@
#### Module over α
@@@ -/

instance [Semiring α] : Module α (Tuple α n) :=
{
  --smul := fun a x => ⟨fun i => a * x i⟩,
  smul_add := by intros a x y; ext i; apply mul_add,
  add_smul := by intros a b x; ext i; apply add_mul,
  mul_smul := by intros a b x; ext i; apply mul_assoc,
  one_smul := by intros x; ext i; apply one_mul,
  zero_smul := by intros x; ext i; apply zero_mul,
  smul_zero := by intros a; ext i; apply mul_zero
}

/- @@@
#### Additive Monoid

It turned out we'd need this for a proof of zero_add
and add_zero
@@@ -/
instance [AddMonoid α] : AddMonoid (Tuple α n) where
  zero := ⟨ fun _ => 0 ⟩
  add := (· + ·)
  nsmul := nsmulRec
  zero_add := by intros; ext; apply zero_add
  add_zero := by intros; ext; apply add_zero
  add_assoc := by intros; ext; apply add_assoc

/- @@@
### Test
@@@ -/

def t1 : Tuple ℚ 3 := ⟨ aFinTuple ⟩
#eval 3 • (t1 + (1/2 :ℚ) • t1 )         -- nsmul (nat smul)
#eval (3 : ℚ) • (t1 + (1/2 :ℚ) • t1 )   --HSMul (notation)



----------------------------------------------------
/- @@@
## Vector: Vc α n

We now define our abstract vector type, *Vc α n*, in
the same way, but now using *Tuple α n* as a concrete
representation. We lift the operations and structures
we need from the underlying *Tuple* type, just as did
for *Tuple* from he underlying scalar *K* type.
@@@ -/

/- @@@
### Data
@@@ -/

@[ext]
structure Vc (α : Type u) (n : Nat) : Type u where
  (toRep : Tuple α n)
deriving Repr, DecidableEq --, BEq

/- @@@
### Operations
@@@ -/

/- @@@
Retracted.
```lean
  -- Coerce a Tuple back to its underlying rep type
instance :
  CoeFun (Vc α n) (fun _ => Tuple α n) :=
    { coe v := v.toRep }
```
@@@ -/

instance [Zero α]: Zero (Vc α n) where
  zero := ⟨ 0 ⟩

instance [Add α] : Add (Vc α n) where
  add t1 t2 := ⟨ t1.1 + t2.1 ⟩

instance [Neg α] : Neg (Vc α n) where
   neg t := ⟨ -t.1 ⟩

-- maths
instance [Sub α] : Sub (Vc α n) where
 sub t v := ⟨ t.1  - v.1  ⟩

-- TODO: glitch here?
instance [SMul α α] : SMul α (Vc α n) where
  smul a t := ⟨ a • (t.1 : Tuple α n) ⟩


-- TODO: Needed????
-- instance [Add α] : HAdd (Vc α n) (Vc α n) (Vc α n) where
--   hAdd := Add.add

-- instance [Sub α] : HSub (Vc α n) (Vc α n) (Vc α n)  where
--   hSub t v := ⟨ t - v ⟩

/- @@@
### Structures
@@@ -/

/- @@@
#### AddCommSemigroup
@@@ -/

instance [AddCommSemigroup α]: AddCommSemigroup (Vc α n) :=
{
  add_comm := by     -- So you can see the steps
    intros
    ext i
    apply add_comm
  add_assoc := by intros; ext; apply add_assoc
}

/- @@@
#### AddCommMonoid
@@@ -/
instance [AddCommMonoid α] : AddCommMonoid (Vc α n) :=
{
  add := Add.add
  zero := Zero.zero
  nsmul := nsmulRec
  add_assoc := by intros; ext; apply add_assoc
  zero_add := by intros; ext; apply zero_add
  add_zero := by intros; ext; apply add_zero
  add_comm := by intros; ext; apply add_comm
}

/- @@@
#### Module α (Vc α n)
@@@ -/
instance [Semiring α] : Module α (Vc α n) :=
{
  --smul := fun a x => ⟨fun i => a * x i⟩,
  smul_add := by intros a x y; ext i; apply mul_add,
  add_smul := by intros a b x; ext i; apply add_mul,
  mul_smul := by intros a b x; ext i; apply mul_assoc,
  one_smul := by intros x; ext i; apply one_mul,
  zero_smul := by intros x; ext i; apply zero_mul,
  smul_zero := by intros a; ext i; apply mul_zero
}

/- @@@
### Vector Space

Yay! We have defined *Vc* as a module over α (where
α is the scalar type). Now whenever α is a field, we
have a *vector space*. For example, if we let α = ℚ,
then we have a vector space, as ℚ is a field under all
of the usual definitions of arithmetic. We can define
an abbreviation should we wish to reify this notion.
@@@ -/

abbrev VectorSpace K V [Field K] [AddCommMonoid V] := Module K V

/- @@@
### Examples
@@@ -/

#synth (VectorSpace ℚ (Vc ℚ 3))      -- Found
#synth (VectorSpace ℚ (Tuple ℚ 3))   -- Found
#synth (VectorSpace ℚ (Fin n → ℚ))   -- Found

/- @@@
@@@ -/

-- Yay
-- Now that we can have Vc as the type of p2 -ᵥ p1
-- with p1 p2 : Pt
-- We can have Torsor Vc Pt
-- And that is affine space for any Vc sastisfying and Pt satisfying









----------------------------------------------

/- @@@
## Pt α n
@@@ -/

/- @@@
## Points: Pt α n

We will now represent n-dimensional α *points* * as
n-tuples of α values in the same way.

### Data Type
@@@ -/

@[ext]
structure Pt (α : Type u) (n: Nat) where
  (toRep: Tuple α n)
deriving Repr, DecidableEq --, BEq

/- @@@
### Overloads
@@@ -/

/- @@@
```lean
-- A coercion to extract the (Fin n → α) representation
instance : Coe (Pt α n) (Tuple α n) where
  coe := Pt.toRep
```
@@@ -/

/- @@@
## α Affine n-Spaces
@@@ -/


-- TODO: Validate
instance [Zero α] : Nonempty (Pt α n) := Nonempty.intro ⟨ 0 ⟩


-- instance [Add α] : HAdd (Vc α n) (Pt α n) (Tuple α n) where
--   hAdd v p := v + (p : Tuple α n)

-- TODO: Keep?
-- There will be no add operation on points, however
-- there is heterogeneous add, of vectors to points
-- instance [Add α] [HAdd α α α] : HAdd (Vc α n) (Pt α n) (Pt α n) where
--   hAdd v p := ⟨ v + p ⟩

-- now we need VSub all the way down
instance [Sub α] [VSub α α]: VSub (Vc α n) (Pt α n) :=
{
  vsub p2 p1 := ⟨ p2.1 - p1.1 ⟩
}

-- instance [Add α] : HAdd (Vc α n) (Pt α n) (Tuple α n) :=
--   { hAdd := λ v p => v + (p : Tuple α n) }

-- instance [Add α] : HVAdd (Vc α n) (Pt α n) (Pt α n) where
--   hVAdd := λ v p => ⟨ v + p ⟩

/- @@@
Whoa, now we're driven to implement AddMonoid Tuple to
finish provers in AddTorsor. You can find the code we had
to add at the end of the operations part. See the above.
@@@ -/

/-
Just found we need to define HAdd all the way up, including to HAdd (Fin n → α) (Fin n → α)
-/

-- Be sure the assumed typeclass instances are already provided
--
-- Then add the missing fields and values for them
-- Do as much as you can by simple reduction to corresponding actions on concrete representations

instance [Add α] : VAdd (Vc α n) (Pt α n) where
  vadd v p := ⟨ v.1 + p.1⟩

theorem Vc.vadd_pt_def [Add α] (v : Vc α n) (p : Pt α n) : v +ᵥ p = ⟨v.1 + p.1⟩ := rfl

instance : AddGroup (Vc α n) := sorry

instance [Add α] [Zero α] -- ) (Tuple α n) (Tuple α n)]
  [Nonempty (Pt α n)] :
  AddTorsor (Vc α n) (Pt α n) :=
{
  vadd v p := ⟨ v.1 + p.1 ⟩

  zero_vadd := by
    intros p
    ext i
    simp [HVAdd.hVAdd, HAdd.hAdd, VAdd.vadd]
    _

  add_vadd := by
    _

  vsub:= by
    _

  vsub_vadd':= by
    _

  vadd_vsub':= by
    _
}


/- @@@
### Starter Example

To give you a good start on the overall task, here's
a completed construction showing that our Vc vectors
form an additive monoid. We already have a definition
of *+*. We'll need a proof that *+* is associative, so
let's see that first.
@@@ -/

theorem vcAddAssoc {α : Type u} {n : Nat} [Ring α]:
  ∀ (v1 v2 v3 : Vc α n), v1 + v2 + v3 = v1 + (v2 + v3) := by
  -- Assume three vectors
  intro v1 v2 v3
  -- strip Vc and Tuple abstraction
  apply congrArg Vc.mk
  apply congrArg Tuple.mk
  /- @@@
  NB: We now must show equality of  underlying Fin n → α
  *functions*. For this we're going to need an axiom that
  is new to us: the axiom of *functional extensionality*.
  What it says is if two functions produce the same outputs
  for all inputs then they are equal (even if expressed in
  very different ways). Look carefully at the goal before
  and after running *funext*.
  @@@ -/
  apply funext
  -- Now prove values are equal for arbitrary index values
  intro i
  -- This step is not necessary but gives better clarity
  simp [HAdd.hAdd]
  -- Finally appeal to associativity of α addition
  apply add_assoc
  /- @@@
  Go read the add_assoc theorem and puzzle through how
  its application here finishes the proof.
  @@@ -/

/- @@@
With that, we're two steps (*add* and *add_assoc*) closer
to showing that our n-Dimensional vectors form a Monoid (as
long as α itself has the necessary properties (e.g., that the
α + is associative). We ensure that by adding the precondition
that α be a Ring. That will ensure that α has all of the usual
arithmetic operations and proofs of properties.
@@@ -/

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

/- @@@
Yay. Vc forms an additive monoid.
@@@ -/

/- @@@
### Your Job

TODO: Continue with the main task. A precondition for forming
an additive torsor is to show that Vc forms an additive group.
You might want to start with that!
@@@ -/

instance {α : Type u} {n : Nat} [Ring α]: AddGroup (Vc α n) :=
{
}

instance {α : Type u} {n : Nat} [Ring α]: AddTorsor (Vc α n) (Pt α n) :=
{
}


/- @@@
## Alternative Rep: Finsupp: ℕ →₀ K

### Data Type
In Lean, (ℕ →₀ K) is notation for Finsupp ℕ K,
the type of functions from ℕ to K that are defined
on only a finite number of ℕ inputs. That set is
called the *support* of such a function. The name
of type thus makes sense: It's the type of functions
with finite support. The index set, here ℕ, can be
any type, not just *Fin n*.

### Structures

Lean pre-defines a range of important structures
on Finsupp types.
@@@ -/

#synth (AddCommGroup (ℕ →₀ K))
#synth (Semiring K)
#synth (Module K (Fin _ → K)) -- Yes with Fin n → K
-- #synth (Module K (ℕ →₀ K))) -- No with ℕ →₀ K

/- @@@
### Fin n → K vs ℕ →₀ K

Proofs where tuples are represented as *(ℕ →₀ K)* functions
can be more tedious than with *(Fin n → K)* representations.
Definining computation is also harder with (ℕ →₀ K).

A benefit is that Lean defines what it means to be a *basis* for
a space of tuples of type *(ℕ →₀ K)*. We will have to define our
own notion of basis for spaces using *Fin n → K* tuples. If one
is working with sparse vectors even in infinite dimensional
spaces,  ℕ →₀ K, as long as no functions have more than finite
support.
@@@ -/

/- @@@
Ack. Thank you: Rob_23oba.
@@@ -/
