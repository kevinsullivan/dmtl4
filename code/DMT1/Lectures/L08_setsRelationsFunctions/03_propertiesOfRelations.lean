import Mathlib.Data.Rel
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Real.Basic

/- @@@
# Properties of Binary Relations

There are many important properties of relations. In this
section we'll formally define some of the most important.
The definitions/specifications speak for themselves.

<!-- toc -->

@@@ -/

namespace DMT1.Lectures.setsRelationsFunctions.propertiesOfRelations

/- @@@

## Properties of Binary Relations in General
@@@-/

/- @@@
The property of a relation not relating any pair of values.
We call such a relation *empty.*
@@@ -/
def isEmpty {α β : Type} : Rel α β → Prop :=
  fun (r : Rel α β) => ¬∃ (x : α) (y : β), r x y

/- @@@
The property of a relation relating every pair of values.
We call such a relation *complete*. NOTE: We've corrected
the previous chapter, which used the term *total* for such
a relation. Use *complete* as we will define *total* to be
a different property.
@@@ -/
def isComplete {α β : Type} : Rel α β → Prop :=
  fun r => ∀ x y, r x y


-- Example, the complete relation on natural numbers
def natCompleteRel : Rel Nat Nat := fun a b => True

-- A proposition and a proof that it is complete
example : isComplete natCompleteRel :=
/- @@@
By the definition of isComplete we need to prove that
every pair is in this relation. In other words, we need
to prove, *∀ (a b : Nat), natCompleteRel a b*. This is
a universally quantified proposition, so we apply the
rule for ∀, which is to assume arbitrary values of the
arguments, *a,, b,* and then show *natCompleteRel a b*.
@@@ -/
fun a b =>
  True.intro

/- @@@
A relation is said to be *total* if it relates every
value in its domain of definition to some output value.
In other words, a relation is total if its *domain* is
its entire *domain of definition*.
@@@ -/
def isTotal  {α β : Type} : Rel α β → Prop :=
  fun r => ∀ (x : α), ∃ (y : β), r x y


/- @@@
A relation is called *surjective* if it relates some
input to *every* output in its codomain. That is, for
every output, there is some input that is related to it.
@@@ -/
def isSurjectiveRel {α β : Type} : Rel α β → Prop :=
  fun r => ∀ (y : β), ∃ (x : α), r x y


/- @@@
A binary relation is said to be *single-valued* if no
input is related to more than one *output*. This is the
property that crucially distinguishes binary relations
that are also mathematical *functions* from those that
are just relations but not functions. The way we express
this property is slightly indirect. It says that to be
a function means that there cannot be two outputs for
a single input unless those outputs are actually the same,
in which case there's just one.
@@@ -/
def isSingleValued {α β : Type} : Rel α β → Prop :=
  fun r => ∀ x y z, r x y → r x z → y = z

/- @@@
A relation is said to be *injective* if there is no
more than one input that is related to any given output.
Such a relation is also called *one-to-one*, as distinct
from *many-to-one*, which injectivity prohibits.
@@@ -/
def isInjectiveRel  {α β : Type} : Rel α β → Prop :=
  fun r => ∀ x y z, r x z → r y z → x = y

/- @@@
## Properties of Functions in Particular
@@@ -/


/- @@@
The property of being a function, i.e., single-valued
@@@ -/
def isFunctional {α β : Type} : Rel α β → Prop :=
  isSingleValued


-- The term injective is usually applied only to functions
def isInjective {α β : Type} : Rel α β → Prop :=
  fun r => isFunctional r ∧ isInjectiveRel r


-- The term surjective is usually applied only to functions
def isSurjective {α β : Type} : Rel α β → Prop :=
  fun r => isFunctional r ∧ isSurjectiveRel r


-- "One to one" is another name for injectivity
def isOneToOne {α β : Type} : Rel α β → Prop :=
  isInjective


-- "Onto" is another name for surjectivity
def isOnto {α β : Type} : Rel α β → Prop :=
  isSurjective


-- property of a *function* pairing domain and range values
def isBijective {α β : Type} : Rel α β → Prop :=
  fun r => isInjective r ∧ isSurjective r
/- @@@
When a relation is a function and is both injective
and surjective then the relation defines a pairing of
the elements of the two sets. Among other things, the
existence of a bijective relationship shows that the
domain and range sets are the same size.
@@@ -/


/- @@@
## More Properties of Relations in General
@@@ -/

-- The property of a relation being a many-to-one function
def isManyToOne {α β : Type} : Rel α β → Prop :=
  fun r => ¬isInjective r


-- The property of being a one-to-many injection
def isOneToMany {α β : Type} : Rel α β → Prop :=
  fun r => ¬isFunctional r ∧ isInjectiveRel r


-- The property of being a many-to-many relation
def isManyToMany {α β : Type} : Rel α β → Prop :=
  fun r => ¬isFunctional r ∧ ¬isInjectiveRel r


/- @@@
Properties of Binary Relations on a Single Set/Type
@@@ -/

-- The property of relating every input to itself
def isReflexive {α β : Type} : Rel α α → Prop :=
  fun r => ∀ (a : α), r a a


-- The property, if (a, b) ∈ r then (b, a) ∈ r
def isSymmetric {α β : Type} : Rel α α → Prop :=
  fun r => ∀ (a b : α), r a b → r b a


-- The property, if (a, b) ∈ r and (b, c) ∈ r then (a, c) ∈ r
def isTransitive {α β : Type} : Rel α α → Prop :=
  fun r =>  ∀ (a b c : α), r a b → r b c → r a c


-- The property of partitioning inputs into equivalence classes
def isEquivalence {α  β : Type} : Rel α α → Prop :=
  fun r => (@isReflexive α β r) ∧
           (@isSymmetric  α β r) ∧
           (@isTransitive α β r)


-- The property, if (a, b) ∈ r then (b, a) ∉ r
def isAsymmetric {α  β : Type} : Rel α α → Prop :=
  fun r => ∀ (a b : α), r a b → ¬r b a


-- The property, if (a, b) ∈ r and (b, a) ∈ r then a = b
def isAntisymmetric {α  β : Type} : Rel α α → Prop :=
  fun r => ∀ (a b : α), r a b → r b a → a = b

/- @@@
The property of a relation that relates every pair
of values one way or the other
@@@ -/
def isStronglyConnected {α  β : Type} : Rel α α → Prop :=
  fun r => ∀ (a b : α), r a b ∨ r b a

def isPartialOrder {α  β : Type} : Rel α α → Prop :=
  fun r =>
    @isReflexive α β r ∧
    @isAntisymmetric α β r ∧
    @isTransitive α β r

def isTotalOrder {α  β : Type} : Rel α α → Prop :=
  fun r =>
    @isPartialOrder α β r ∧
    @isStronglyConnected α β r

def isLinearOrder {α  β : Type} := @isTotalOrder α β

def isWellFounded  {α  β : Type} : Rel α α → Prop :=
  fun r => ∀ (s : Set α), s ≠ ∅ → ∃ m, (m ∈ s ∧ ¬∃ n ∈ s, r n m)

-- See [TPIL4](https://leanprover.github.io/theorem_proving_in_lean4/induction_and_recursion.html#well-founded-recursion-and-induction).

def predRel : Rel Nat Nat := fun a b => b = a.succ


example : @isWellFounded Nat Nat predRel :=
  fun s nonempty =>
  -- ∃ m ∈ s, ¬∃ n ∈ s, predRel n m
  sorry

/- @@@
## Examples
@@@ -/


/- @@@
## Example: Equality is an equivalence relation.


To show that that equality on a type, α, (@Eq α), is
an equivalence relation, we have to show that it's
reflexive, symmetric, and transitive. We'll give the
proof in a bottom up style, first proving each of the
conjuncts, then composing them into a proof of the
overall conjecture.
@@@ -/

-- equality is reflective
theorem eqIsRefl {α β: Type}: @isReflexive α β (@Eq α) :=
  -- prove that for any a, a = a
  fun (a : α) => rfl

-- equality is symmetric
theorem eqIsSymm {α β: Type}: @isSymmetric α β (@Eq α) :=
  -- prove that for any a, b, if a = b ∈ r then b = a
  -- use proof of a = b to rewrite a to b in b = a
  -- yielding b = b, which Lean then proves using rfl
  fun (a b : α) (hab : a = b) => by rw [hab]

-- equality is transitive
theorem eqIsTrans {α β: Type}: @isTransitive α β (@Eq α) :=
  -- similar to last proof
  fun (a b c : α) (hab : a = b) (hbc : b = c) => by rw [hab, hbc]

-- equality is an equivalence relation
theorem eqIsEquiv {α β: Type}: @isEquivalence α β (@Eq α) :=
  -- just need to prove that Eq is refl,, symm, and trans
  ⟨ eqIsRefl, ⟨ eqIsSymm, eqIsTrans ⟩ ⟩ -- And.intros

/- @@@
### The Property of Being Empty

Any emptyRel (see our definition) has the property of being empty.
@@@ -/
def emptyRel {α β : Type*} : Rel α β := fun _ _ => False

example {α β : Type} : @isEmpty α β emptyRel :=
  -- To prove: ¬∃ x y, r x y
  -- Proof by negation: assume ∃ x y, emptyRel x y
  fun (h : ∃ x y, emptyRel x y) =>
    -- show that that can't happen
    -- proof by ∃ elimination to get argument a
    Exists.elim h
      fun (a : α) (exy : ∃ y, emptyRel a y) =>
        -- proof by ∃ elimination to get argyment b
        Exists.elim exy
          -- proof of (a, b) ∈ emptyRel cannot be
          fun b pfBad => nomatch pfBad


/- @@@
### The Set.subset Relation is a Partial Order
@@@ -/

def subSetRel {α : Type} : Rel (Set α) (Set α) :=
  fun (s t : Set α) => s ⊆ t

#reduce (types:=true) subSetRel

-- remember that we need β for any Rel but it's irrelevan here
example {α β : Type}: (@isPartialOrder (Set α) β) (@subSetRel α)  :=
  And.intro
    -- @isReflexive α β r ∧
    -- by the definition of isReflexive, show ∀ a, r a a
    (fun s =>               -- for any set
      fun a =>              -- for any a ∈ s
        fun ains => ains    -- a ∈ s
    )
    (
      And.intro
        -- @isAntisymmetric α β r ∧
        -- ∀ (a b : α), r a b → r b a → a = b
        (
          fun (s1 s2 : Set α)
              (hab : subSetRel s1 s2)
              (hba : subSetRel s2 s1) =>
            (
              Set.ext   -- axiom: reduces s1 = s2 to bi-implication
              fun a =>
                Iff.intro
                  (fun h => hab h)
                  (fun h => hba h)
            )
        )
        -- @isTransitive α β r
        -- ∀ (a b c : α), r a b → r b c → r a c
        (
          (
            fun s t v hst htv =>
            (
              fun a =>  -- for any member of a
                fun has =>
                  let hat := hst has
                  htv hat
            )
          )
        )
    )

/- @@@
### The inverse of an injective function is a function
@@@ -/

#check Rel.inv
example {α β : Type} :
  ∀ (r : Rel α β),
    isInjective r →
    isFunctional (r.inv) :=
  fun r =>              -- assume r is any relation
  fun hinjr =>          -- and that it's injective
  -- show inverse is a function
  -- assume r output, r.inv input, elements c b a
  fun c b a =>
  -- we need to show that r.inv is single valued
  -- assume r.inv associatss c with both b and a
      fun rinvcb rinvca =>
        -- show b = a
        have rac : r a c := rinvca
        have rbc : r b c := rinvcb
        -- ∀ x y z, r x y → r x z → y = z
        have rfun : isFunctional r := hinjr.left
        sorry ---???

end DMT1.Lectures.setsRelationsFunctions.propertiesOfRelations
