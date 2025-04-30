import Init.Data.Repr
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.AffineSpace.Defs
import Mathlib.Algebra.Module.Pi



/- @@@
# α Affine n-Space

We'll assume *n* is a natural number representing the
dimension of the space we want to construct.
@@@ -/

variable
  {n : Nat}
  {α : Type u}

/- @@@
## Scalars

Throughout the rest of this file, let α represent any type that
we intend to use as scalars, and let  *n* represent the dimension
of any tuple or vector or affine space we wish to construct.

Lean already knows a lot of the structures on such types as the
rational, ℚ. For example, Lean's libraries already enable it to
synthesize an *AddGroup* structure on ℚ. That means we already
have definitions of not only the standard arithmetic operations
(such as *add*, with notation *+*) on ℚ, but we also have *proofs*
of, e.g., all of the group axioms for ℚ (add is associative, etc).
@@@ -/

-- #synth (AddGroup ℚ)
-- #synth (HAdd ℚ ℚ ℚ)



---------------------------------------------------

/- @@@
## Fin n → α

Lean also has predefined algebraic structures on *Fin n → α*.
Here for example we confirm that Lean can synthesize an additive
group structure on (Fin n → α). That means first we can add, negate,
subtract, and scalar multiply (by Nat or Int) these things. Second,
we can have proofs of all the (here) *group axioms* for (Fin n → α).
@@@ -/

-- #synth (AddGroup (Fin (_ : Nat) → ℚ))

/- @@@
There's more going on here than meets the eye. To synthesize a
group structure on *Fin n → α* depends on there being a group
structure on *α* itself. As an example, that (Fin n → α) tuple
encodings forms a group means the must be addition on (Fin n → α).
Lean defines that by *pointwise* addition using the addition that
is defined for the scalar type, α, requiring of course that there
also be an addition operation for individual α values. Of course
that is the case when α = ℚ, as we've already seen.
@@@ -/

-- #synth (AddCommSemigroup (Fin (_ : Nat) → ℚ))
-- #synth (AddCommMonoid (Fin (_ : Nat) → ℚ))
-- #synth (HAdd ℚ ℚ ℚ)     --yes
-- #synth (HAdd (Fin (_ : Nat) → ℚ) (Fin (_ : Nat) → ℚ) (Fin (_ : Nat) → ℚ)) --no

/- @@@
## α n-tuples

We will use Fin n → α to represent tuples.
@@@ -/


-- Pretty printing (ignore details)
instance [Repr α] : Repr (Fin n → α) where
  reprPrec t _ := repr (List.ofFn t)


/- @@@
We're going to want to have a definition of zero for
Fin n → α. It's not pre-defined in Lean's libraries.
@@@ -/

-- No need to define any of this for (Fin n → ℚ)
-- #synth (Zero (Fin n → ℚ))
-- #synth (Add (Fin n → ℚ))
-- #synth (HAdd (Fin n → ℚ) (Fin n → ℚ) (Fin n → ℚ))

-- We *do* need a definition theorem for (0 : Fin n → α)
theorem Zero.zero_def [Zero α] :
    (0 : Fin n → α) = fun _ => 0 := rfl


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

-- instance [Zero (Fin n → α)] : Zero (Tuple α n) where
--   zero := ⟨ 0 ⟩

instance [Zero α] : Zero (Tuple α n) where
  zero := ⟨ 0 ⟩

/- @@@
When you introduce notation like +, -, •, or +ᵥ, you’re really using syntactic sugar for
typeclass-based operations like HAdd, HSub, SMul, VAdd, VSub, etc. To support these notations
well, and make them usable in proofs, you should pair them with definition theorems that make
the meaning of the operation transparent to the simplifier, the rewriter, and the human reader.
Zero, like some other classes, is its own notation class.
@@@ -/

theorem Tuple.zero_def [Zero α] : (0 : Tuple α n) = ⟨ (0 : Fin n → α) ⟩ := rfl

/- @@@
### Operations
@@@ -/


/- @@@
#### Add

Here we Tuples in terms of addition of their underlying
(Fin n → α) representations, which Lean knows how to do
provided it has a way to add individual α values. That is
providing by passing in an instance of the [Add α] class.

@@@ -/

instance [Add α] : Add (Tuple α n) where
  add t1 t2 := ⟨ t1.1 + t2.1 ⟩   -- Fin n → α add on right

/- @@@
This is important. The *Add* class defines the arithmetic.
One should *also* instantial any separate *notation-defining*
class. The `+` notation is actually defined by the *HAdd*

Support for `+` notation using HAdd class. They key idea to
observe here is that we want the hAdd operation (addition
using `+`) to use precisely the same definition of Tuple
addition defined in the *Add* class. The pattern to use is
first to define the arithmetic class, and then to define
the notation class, ensuring that it's notational operator
is simply *delegating* to the actual arithmetic definition.
Follow this pattern thoughout, and going forward.
@@@ -/
instance [Add α] : HAdd (Tuple α n) (Tuple α n) (Tuple α n) where
  hAdd := Add.add

/- @@@
Finally, write a corresponding *definition theorem* to provide
a known basis for rewriting and simplifying expressions using
the concrete notation. If you want the *simp* tactic to know
about and use this rewriting rule, annotate the definition with
*@[simp]*. We prefer to disable most such automations here so
as to see exactly what's going on at all times.

@@@ -/

theorem Tuple.add_def [Add α] (t1 t2 : Tuple α n) :
  t1 + t2 = ⟨ t1.1 + t2.1 ⟩ := rfl

/- @@@
HAdd is synthesized, but not its definition theorem. Marking
it as a simp axioms mean it'll be used as part of simp.
@@@ -/

-- @[simp]
theorem Tuple.hAdd_def [Add α] (x y : Tuple α n) :
  HAdd.hAdd x y = ⟨ x.1 + y.1 ⟩ := rfl


/- @@@
#### Neg

Now another small complication. Not every arithmetic-defining
class, such as *Add*, has a separate notation class. There is
no separate notation defining class (which would presumably be
called *HNeg*) like there is for binary HAdd. Rather, the *-*
notation is provided by *Neg* itself. Separate notation classes
are used when there are both homogeneous versions of operations
(such as + : α → α → α) and heterogeneous (e.g., + : α → β → γ).
Unary negation, being unary, is always homogeneously typed, so
no separate notation class is needed or provided.
@@@ -/

instance [Neg α] : Neg (Tuple α n) where
   neg t := ⟨ -t.1 ⟩

theorem Tuple.neg_def [Neg α] (t : Tuple α n) :
  -t = ⟨ -t.1 ⟩ := rfl


/- @@@
#### Sub
@@@ -/

instance [Sub α] : Sub (Tuple α n) where
  sub t1 t2 := ⟨t1.1 - t2.1⟩

instance [Sub α] : HSub (Tuple α n) (Tuple α n) (Tuple α n) :=
{
  hSub := Sub.sub
}

-- @[simp]
theorem Tuple.sub_def [Sub α] (t1 t2 : Tuple α n) :
  t1 - t2 = ⟨t1.1 - t2.1⟩ := rfl

/- @@@
#### SMul

SMul is its own notation class.
@@@ -/

instance [SMul α α] : SMul α (Tuple α n) where
  smul a t := ⟨ a • t.1 ⟩

/- @@@
Yet more complexity: Lean will automatically infer an HSMul
(notation-providing) instance from this SMul instance via a
SMul.toHSMul instance know to Lean. So there's no need, and
it would be undesirable to define HSMul. By contrast, Lean
does not automatically derive an *HAdd* instances from *Add*,
so we defined *HAdd* explicitly. We've thus commented out the
notation class definition that we might otherwise write here.
@@@ -/
-- instance [SMul α α] : HSMul α (Tuple α n) (Tuple α n) :=
-- {
--   hSMul := SMul.smul
-- }

/- @@@
We do still want to give ourselves a well known operation for
reducing a • t on tuples to the level of Fin n → α operations,
which we do with this *definition theorem*.
@@@ -/
-- @[simp]
theorem Tuple.smul_def [SMul α α] (a : α) (t : Tuple α n) :
  a • t = ⟨ a • t.1 ⟩ := rfl




/- @@@
### Structures
@@@ -/

/- @@@
#### AddCommSemigroup (Tuple α n)
@@@ -/

instance [AddCommSemigroup α] : AddCommSemigroup (Tuple α n) :=
{
/- @@@
Here's a key example of lifing *proofs* from the
level of concrete representation to the level of
*Tuple* objects.

In particular, we'll prove that our tuples form an
additive, commutative semigroup, which is to say that
we'll construct proofs of the axioms for our *Tuples*
from corresopnding proofs for *Fin n → α*.

Those proofs, in turn, will come from an instance
of *AddCommSemigroup *(Fin n → α)* that Lean will
synthesize for us given that the necessary operations
are already available on scalar (α) values. For that,
we tell Lean to provide a *[AddCommSemigroup α]* class
instance, which it can also synthesize on its own.


The proofs of commutative and associativity of addition
on *Tuple* values are then constructed using the proofs
of the corresponding properties for (Fin n → α) concrete
representation objects.

strip the *Tuple* abstraction
using the extensionality axiom for *Tuple* then
apply the corresponding theorem from the level of
the concrete representation. The *ext* tactic is
enabled by the *@[ext]* annotation we've attached
to the *Tuple* type definition. Use *ext* instead
of *apply congrArg Tuple.mk*. Now you know what it
actually does.
@@@ -/
  add_comm := by
    intro a b
    simp [Tuple.add_def]
    apply add_comm

/- @@@
Here we see the use of our definition axiom. If
we replace *simp [Tuple.add_def]* with *ext* then
the extensionality principle will be applied, but
it will erase abstractions all the way to scalars,
not just one level to *Fin n → α*. Consistent with
our wanting a strictly layered architecture here,
we will prefer to strip abstractions just one level
and to use the proofs and values available there.

EXERCISE: Give it a try and in each case study the
goal after applying either variant. Hover over the
elements of the goal to see that in one case you've
got a proof to construct involving (Fin n → α) and
in the other case, involving scalars. There's an
*add_comm* proof available in either case, but one
applies to *Fin n → α* values while the other is on
bare *α* values. It's important to know exactly how
things are simplifying!
@@@ -/

  -- We can write such tactic scripts as one-liners
  add_assoc := by
    intros
    simp [Tuple.add_def]
    apply add_assoc
}

/- @@@
#### AddCommMonoid (Tuple α n)
@@@ -/

instance [AddCommMonoid α]: AddCommMonoid (Tuple α n) :=
{
  nsmul := nsmulRec

  zero_add := by
    intros
    simp [Tuple.add_def, Tuple.zero_def]

  add_zero := by
    intros
    simp [Tuple.add_def, Tuple.zero_def]
}

-- CLASS 4/22 ENDED HERE

/- @@@
#### Module α (Tuple α n)
@@@ -/

instance [Semiring α] : Module α (Tuple α n) :=
{
  smul_add := by
    intros
    simp [Tuple.smul_def]
    simp [Tuple.add_def]
  add_smul := by intros; simp [Tuple.smul_def, Tuple.add_def]; apply add_mul,
  mul_smul := by intros; simp [Tuple.smul_def, Tuple.add_def]; apply mul_assoc,
  one_smul := by intros; simp [Tuple.smul_def]
  zero_smul := by intros; simp [Tuple.zero_def, Tuple.smul_def]
  smul_zero := by intros a; simp [Tuple.zero_def, Tuple.smul_def]
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
theorem Vc.zero_def [Zero α] :
  (0 : Vc α n) = ⟨ ( 0 : Tuple α n) ⟩ := rfl

/- @@@
### Operations
@@@ -/


/- @@@
#### Add
@@@-/

instance [Add α] : Add (Vc α n) where
  add t1 t2 := ⟨ t1.1 + t2.1 ⟩


-- SIMP ENABLED HERE
-- @[simp]
theorem Vc.add_def [Add α] (t1 t2 : Vc α n) :
  t1 + t2 = ⟨ t1.1 + t2.1 ⟩ := rfl

/- @@@
#### HAdd
@@@-/

-- Support for Vc `+` notation using HAdd
instance [Add α]  : HAdd (Vc α n) (Vc α n) (Vc α n) :=
{
  hAdd := Add.add
}

-- @[simp]
theorem Vc.hAdd_def [Add α] (v w : Vc α n) :
  HAdd.hAdd v w = ⟨ v.1 + w.1 ⟩ := rfl

/- @@@
#### Neg
@@@-/

/- @@@
#### Neg
@@@ -/

instance [Neg α] : Neg (Vc α n) where
   neg t := ⟨ -t.1 ⟩

theorem Vc.neg_def [Neg α] (t : Tuple α n) :
  -t = ⟨ -t.1 ⟩ := rfl



/- @@@
#### Sub
@@@ -/

instance [Sub α] : Sub (Vc α n) where
  sub t1 t2 := ⟨t1.1 - t2.1⟩

-- @[simp]
theorem Vc.sub_def [Sub α] (t1 t2 : Vc α n) :
  t1 - t2 = ⟨t1.1 - t2.1⟩ := rfl


/- @@@
#### SMul

SMul is its own notation class.
@@@ -/

instance [SMul α α] : SMul α (Vc α n) where
  smul a t := ⟨ a • t.1 ⟩

-- @[simp]
theorem Vc.smul_def [SMul α α] (a : α) (t : Vc α n) :
  a • t = ⟨ a • t.1 ⟩ := rfl


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
    simp [Vc.add_def]
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

We're not going to define
@@@ -/

instance [Sub α] : VSub (Tuple α n) (Tuple α n) :=
{
  vsub p2 p1 := ⟨ p2.1 - p1.1 ⟩
}

theorem Tuple.vsub_def [Sub α] (p2 p1 : Tuple α n) :
  p2 -ᵥ p1 = ⟨ p2.1 - p1.1 ⟩ := rfl

instance [Sub α] : VSub (Vc α n) (Pt α n) :=
{
  vsub p2 p1 := ⟨ p2.1 - p1.1 ⟩
}

theorem Pt.vsub_def [Sub α] (p2 p1 : Pt α n) :
  p2 -ᵥ p1 = ⟨ p2.1 - p1.1 ⟩ := rfl

-- instance [Sub α] [VSub α α] : VSub (Tuple α n) (Tuple α n) :=
-- {
--   vsub p2 p1 := ⟨ p2.1 - p1.1 ⟩
-- }

instance [Sub α] : HSub (Tuple α n) (Tuple α n) (Tuple α n) where
  hSub p q := p - q

/- @@@
#### VAdd
@@@ -/

-- +ᵥ notation
instance [Add α] : VAdd (Tuple α n) (Tuple α n) :=
{
  vadd := Add.add
}

-- SIMP ENABLED
-- @[simp]
theorem Tuple.vadd_def [Add α] (v : Tuple α n) (p : Tuple α n) :
  v + p = ⟨ v.1 + p.1 ⟩ := rfl


-- theorem Tuple.vadd_def [Add α] (t v : Tuple α n) : t + v = ⟨ t.1 + v.1 ⟩ := rfl

-- defines +ᵥ
instance [Add α] : VAdd (Vc α n) (Pt α n) where
  vadd v p := ⟨ v.1 + p.1 ⟩

-- SIMP ENABLED
-- @[simp]
theorem Pt.vadd_def [Add α] (v : Vc α n) (p : Pt α n) :
  v +ᵥ p = ⟨ v.1 + p.1 ⟩ := rfl


/- @@@
## α Affine n-Spaces
@@@ -/

instance [AddMonoid α]: AddAction (Vc α n) (Pt α n) :=
{
  --  (p : Pt α n), 0 +ᵥ p = p
  zero_vadd := by
    intro
    -- to study in part by stepping through
    --
    simp only [Pt.vadd_def]
    simp [Tuple.add_def]
    /- @@@
    Without the only, Lean will go on to simp the tuples, too.
    @@@ -/
    simp [Vc.zero_def]
    simp [Tuple.zero_def]

  -- ∀ (g₁ g₂ : Vc α n) (p : Pt α n), (g₁ + g₂) +ᵥ p = g₁ +ᵥ g₂ +ᵥ p
  -- GOOD EXERCISE
  add_vadd :=  by
    intros
    simp only [Pt.vadd_def]
    simp [Tuple.add_def]
    apply add_assoc
}



#synth (AddMonoid (Vc ℚ n))

-- WIP
-- @[simp]
theorem Pt.add_vadd_def [Add α] (v1 v2 : Vc α n) (p : Pt α n) :
  (v1 + v2) +ᵥ p = ⟨ v1.1 + v2.1 + p.1 ⟩ := rfl


theorem Pt.vsub_vadd'_def
  [Add α]
  [Sub α]
  (p1 p2 : Pt α n) :
   -- match on this
  (p1 -ᵥ p2) +ᵥ p2 =
  -- transofrm to this
  ⟨ (p1.1 - p2.1) + p2.1 ⟩ :=
  by
    simp only [Pt.vadd_def]
    simp only [Pt.vsub_def]


-- AddTorsor (G : outParam Type*) (P : Type*) [AddGroup G] extends AddAction G P, VSub G P
-- Is there already one out there that Lean will synth?
instance

[Nonempty (Pt α n)]
[AddGroup (Vc α n)]
[AddAction (Vc α n) (Pt α n)]
[VSub (Vc α n) (Pt α n)]
:
AddTorsor (Vc α n) (Pt α n) :=
{

  zero_vadd := AddAction.zero_vadd
  add_vadd := AddAction.add_vadd
  vsub:= VSub.vsub
  vsub_vadd':= by
    --  ∀ (p₁ p₂ : Pt α n), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
    intros p1 p2
    sorry

  vadd_vsub':=
    sorry
}


/- @@@
Ack. Thank you: Rob_23oba.
@@@ -/
