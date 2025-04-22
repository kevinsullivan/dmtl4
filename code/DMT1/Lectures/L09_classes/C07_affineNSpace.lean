import Init.Data.Repr
import Mathlib.Data.Rat.Defs

import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.AffineSpace.Defs
import Mathlib.Algebra.Module.Pi


/- @@@
# α Affine n-Space
@@@ -/

/- @@@
## Carrier Type and Dimension

Throughout the rest of this file, let α represent any type and
*n* any natural number dimension of a space.
@@@ -/
variable
  {α : Type u}
  {n : Nat}



/- @@@
## Scalars: α
@@@ -/

/- @@@
## α n-tuples

We will use Fin n → α to represent tuples.
@@@ -/


-- Pretty printing (ignore details)
instance [Repr α] : Repr (Fin n → α) where
  reprPrec t _ := repr (List.ofFn t)


------------------------------------------------------------
-- Tuples
------------------------------------------------------------

/- @@@
## Tuples: Tuple α n

The trick: strip abstractions, construct requirements in the
representation domain then impose the final output abstraction.
The extensionality principle is that two values are equal if their
representations are equal. With the @[ext] annotation you can use
the *ext* tactic to apply this principle, thus stripping the
proof need at the top level down to one needed at the level of
the underlying representation.
@@@ -/


@[ext]
structure Tuple (α : Type u) (n : Nat) where
  toRep : Fin n →  α
deriving Repr

/- @@@
### Values
@@@ -/

-- Pretty printing of values (ignore details)
instance [Repr α] : Repr (Tuple α n) where
  reprPrec t _ := repr (List.ofFn t.1)

/- @@@
#### Zero
@@@ -/

instance [Zero α] : Zero (Tuple α n) where
  zero := ⟨ 0 ⟩

/- @@@
When you introduce notation like +, -, •, or +ᵥ, you’re really using syntactic sugar for
typeclass-based operations like HAdd, HSub, SMul, VAdd, VSub, etc. To support these notations
well, and make them usable in proofs, you should pair them with definition theorems that make
the meaning of the operation transparent to the simplifier, the rewriter, and the human reader.
Zero, like some other classes, is its own notation class. Here is a nice way to write def thms.
@@@ -/

-- theorem Vc.vadd_pt_def [Add α] (v : Vc α n) (p : Pt α n) : v +ᵥ p = ⟨v.1 + p.1⟩ := rfl



/- @@@
### Operations
@@@ -/

/- @@@
#### Add
@@@ -/


-- Define componentwise addition
instance [Add α] : Add (Tuple α n) where
  add t1 t2 := ⟨ t1.1 + t2.1 ⟩   -- Fin n → α add on right

-- Support for `+` notation using HAdd
instance [Add α] : HAdd (Tuple α n) (Tuple α n) (Tuple α n) where
  hAdd := Add.add

-- Definition theorem for simplification and rewriting
-- @[simp]
theorem tuple_add_def [Add α] (t1 t2 : Tuple α n) :
  t1 + t2 = ⟨ t1.1 + t2.1 ⟩ := rfl


/- @@@
#### Neg

PT: There is no separate HNeg like there is for binary HAdd, HSub,
etc., because unary negation is always homogeneously typed.
@@@ -/

instance [Neg α] : Neg (Tuple α n) where
   neg t := ⟨ -t.1 ⟩

theorem tuple_neg_def [Neg α] (t : Tuple α n) :
  -t = ⟨ -t.1 ⟩ := rfl


/- @@@
#### Sub
@@@ -/

instance [Sub α] : Sub (Tuple α n) where
  sub t1 t2 := ⟨t1.1 - t2.1⟩

-- @[simp]
theorem tuple_sub_def [Sub α] (t1 t2 : Tuple α n) :
  t1 - t2 = ⟨t1.1 - t2.1⟩ := rfl

/- @@@
#### SMul

SMul is its own notation class.
@@@ -/

instance [SMul α α] : SMul α (Tuple α n) where
  smul a t := ⟨ a • t.1 ⟩

-- @[simp]
theorem tuple_smul_def [SMul α α] (a : α) (t : Tuple α n) :
  a • t = ⟨ a • t.1 ⟩ := rfl


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
  smul_add := by intros a x y; ext i; apply mul_add,
  add_smul := by intros a b x; ext i; apply add_mul,
  mul_smul := by intros a b x; ext i; apply mul_assoc,
  one_smul := by intros x; ext i; apply one_mul,
  zero_smul := by intros x; ext i; apply zero_mul,
  smul_zero := by intros a; ext i; apply mul_zero
}


/- @@@
@@@ -/
instance [AddGroup α] : AddZeroClass (Tuple α n) :=
{
  zero_add := by
    intros x
    ext
    apply zero_add

  add_zero := by
    intros x
    ext i
    apply add_zero
}



-- Added this to make the following tests work
instance [AddSemigroup α]: AddSemigroup (Tuple α n) :=
{
  add_assoc := by
    intros
    ext
    apply add_assoc
}

/- @@@
#### Additive Monoid

For zero_add and add_zero
@@@ -/
instance [AddMonoid α] : AddMonoid (Tuple α n) :=
{
  nsmul := nsmulRec
  zero_add := by intros; ext; apply zero_add
  add_zero := by intros; ext; apply add_zero
  add_assoc := by intros; ext; apply add_assoc
}

/- @@@
### Test
@@@ -/

def f1 : Fin 3 → ℚ := fun i => match i with |0 => 1/2 |1 => 1/4 |2=> 1/6
def t1 : Tuple ℚ 3 := ⟨ f1 ⟩
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
deriving Repr   --, DecidableEq --, BEq

/- @@@
### Values
@@@ -/

instance [Zero α]: Zero (Vc α n) where
  zero := ⟨ 0 ⟩

-- @[simp]
theorem vec_zero_def [Zero α] :
  (0 : Vc α n) = ⟨ 0 ⟩ := rfl

/- @@@
### Operations
@@@ -/


/- @@@
#### Add
@@@-/

instance [Add α] : Add (Vc α n) where
  add t1 t2 := ⟨ t1.1 + t2.1 ⟩


-- Support for `+` notation using HAdd
instance [Add α] : HAdd (Vc α n) (Vc α n) (Vc α n) where
  hAdd := Add.add


-- Definition theorem for simplification and rewriting
-- @[simp]
theorem vc_add_def [Add α] (t1 t2 : Vc α n) :
  t1 + t2 = ⟨ t1.1 + t2.1 ⟩ := rfl



/- @@@
#### Neg
@@@-/

/- @@@
#### Neg
@@@ -/

instance [Neg α] : Neg (Vc α n) where
   neg t := ⟨ -t.1 ⟩

theorem vc_neg_def [Neg α] (t : Tuple α n) :
  -t = ⟨ -t.1 ⟩ := rfl



/- @@@
#### Sub
@@@ -/

instance [Sub α] : Sub (Vc α n) where
  sub t1 t2 := ⟨t1.1 - t2.1⟩

-- @[simp]
theorem vc_sub_def [Sub α] (t1 t2 : Vc α n) :
  t1 - t2 = ⟨t1.1 - t2.1⟩ := rfl


/- @@@
#### SMul
@@@-/


/- @@@
#### SMul

SMul is its own notation class.
@@@ -/

instance [SMul α α] : SMul α (Vc α n) where
  smul a t := ⟨ a • t.1 ⟩

-- @[simp]
theorem vc_smul_def [SMul α α] (a : α) (t : Vc α n) :
  a • t = ⟨ a • t.1 ⟩ := rfl


instance [SMul α α] : SMul α (Vc α n) where
  smul a t := ⟨ a • (t.1 : Tuple α n) ⟩


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
Had a bug here: included [Add α] as well as [Semigroup α]
thereby getting two equivalent but different definitions
of +. Try adding [Add α] to see how the problem manifests.
@@@ -/
instance [AddSemigroup α] : AddSemigroup (Vc α n) :=
{
  add := Add.add
  add_assoc := by
    intros a b c
    simp [vc_add_def]
    apply add_assoc
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
  smul_add := by intros a x y; ext i; apply mul_add,
  add_smul := by intros a b x; ext i; apply add_mul,
  mul_smul := by intros a b x; ext i; apply mul_assoc,
  one_smul := by intros x; ext i; apply one_mul,
  zero_smul := by intros x; ext i; apply zero_mul,
  smul_zero := by intros a; ext i; apply mul_zero
}

#synth (AddZeroClass ℚ)

instance [AddZeroClass α] : AddZeroClass (Vc α n) :=
{
  zero_add := by
    intros x
    ext i
    apply zero_add


  add_zero := by
    intros x;
    ext i;
    apply add_zero
}

instance [AddMonoid α] : AddMonoid (Vc α n) :=
{
  nsmul := nsmulRec

  zero_add := by
    intro a
    ext
    apply zero_add

  add_zero := by
    intro a
    ext
    apply add_zero
}

/- @@@
Same problem here. Had both [Add α] and [AddSemigroup α],
the latter of which extends [Add α].
@@@ -/
#synth (SubNegMonoid ℚ)

instance [SubNegMonoid α] : SubNegMonoid (Vc α n) :=
{
  zsmul := zsmulRec
  sub_eq_add_neg := by intros a b; ext i; apply sub_eq_add_neg
}

instance [SubNegMonoid α] : SubNegMonoid (Vc α n) :=
{
  zero_add := by
    intro a;
    ext
    apply zero_add

  add_zero := by
    intro a;
    ext
    apply add_zero

  sub_eq_add_neg := by
    intro a b
    ext
    apply sub_eq_add_neg

  nsmul := nsmulRec
  zsmul := zsmulRec

}

instance [AddGroup α] : AddGroup (Vc α n) :=
{
  neg_add_cancel := by
    intro a
    ext
    apply neg_add_cancel
}


-- Yay
-- Now that we can have Vc as the type of p2 -ᵥ p1
-- with p1 p2 : Pt
-- We can have Torsor Vc Pt
-- And that is affine space for any Vc sastisfying and Pt satisfying

----------------------------------------------






/- @@@
## Pt α n

We will now represent n-dimensional α *points* * as
n-tuples of α values in the same way.

### Data Type
@@@ -/

@[ext]
structure Pt (α : Type u) (n: Nat) where
  (toRep: Tuple α n)
deriving Repr   -- , DecidableEq --, BEq

/- @@@
### Values

There are no distinguished point values.
@@@ -/



/- @@@
### Operations
@@@ -/

/- @@@
#### VSub
@@@ -/

instance [Sub α] [VSub α α] : VSub (Vc α n) (Pt α n) :=
{
  vsub p2 p1 := ⟨ p2.1 - p1.1 ⟩
}

-- @[simp]
theorem pt_vsub_def [Sub α] [VSub α α] (t1 t2 : Vc α n) :
  t1 - t2 = ⟨t1.1 - t2.1⟩ := rfl


/- @@@
#### VAdd
@@@ -/

instance [Add α] : VAdd (Vc α n) (Pt α n) where
  vadd v p := ⟨ v.1 + p.1 ⟩


-- @[simp]
theorem pt_vadd_def [Add α] (v : Vc α n) (p : Pt α n) :
  v +ᵥ p = ⟨v.1 + p.1⟩ := rfl


/- @@@
HAdd stuff?
@@@ -/
#synth HAdd ℚ ℚ ℚ

instance [Add α] : HAdd (Fin n → α) (Fin n → α) (Fin n → α) :=
{
  hAdd t v := v + t
}

instance [Add α] : HAdd (Tuple α n) (Tuple α n) (Tuple α n) :=
{
  hAdd t1 t2 := ⟨ t1.1 + t2.1 ⟩
}

instance [Add α] : HAdd (Vc α n) (Pt α n) (Pt α n) :=
{
  hAdd v p := ⟨ v.1 + p.1 ⟩
}

-- [VAdd α α] [HAdd α α α]
instance [Group α] [VAdd α α] [HAdd (Vc α n) (Pt α n) (Pt α n)] [Nonempty (Pt α n)] [AddGroup (Vc α n)]  :
  AddTorsor (Vc α n) (Pt α n) :=
{

  vadd v p := ⟨v.1 + p.1⟩

  zero_vadd := by
    intros p
    apply zero_vadd
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
## α Affine n-Spaces
@@@ -/




/- @@@
Appendix: Operations and Structures Available on Scalars
@@@ -/

/- @@@
### Operations
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
