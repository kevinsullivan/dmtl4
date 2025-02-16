```lean
import Mathlib.Data.Rel
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Real.Basic
```

# Properties of Binary Relations

There are many important properties of relations. In this
section we'll formally define some of the most important.
The definitions/specifications speak for themselves.

<!-- toc -->


```lean
namespace DMT1.Lectures.setsRelationsFunctions.propertiesOfRelations
```

The property of not relating any pair of values
```lean
def isEmpty {α β : Type} : Rel α β → Prop :=
  fun (r : Rel α β) => ¬∃ (x : α) (y : β), r x y
```

The property of relating every every pair of values
```lean
def isComplete {α β : Type} : Rel α β → Prop :=
  fun r => ∀ x y, r x y

def natCompleteRel : Rel Nat Nat := fun a b => True

example : isComplete natCompleteRel :=
-- by the definiteion of isComplete what needs to be proved is
-- ∀ (a b : Nat), natCompleteRel a b
fun a b =>
-- prove natCompleteRel a b
-- by the definition of natCompleteRel
-- what is to be proved is ...
--
True.intro
```

The property of relating every input to some output
```lean
def isTotal  {α β : Type} : Rel α β → Prop :=
  fun r => ∀ (x : α), ∃ (y : β), r x y
```

The property of relating some input to every output
```lean
def isSurjectiveRel {α β : Type} : Rel α β → Prop :=
  fun r => ∀ (y : β), ∃ (x : α), r x y
```

The property of relating no input to more than one output
```lean
def isSingleValued {α β : Type} : Rel α β → Prop :=
  fun r => ∀ x y z, r x y → r x z → y = z
```

The property of relating no more than one input to any
output. Sometimes also called one-to-one, as distinct
from many-to-one, which injectivity prohibits.
```lean
def isInjectiveRel  {α β : Type} : Rel α β → Prop :=
  fun r => ∀ x y z, r x z → r y z → x = y
```

The propery of a relation being surject means that there
is at least one input, a, for each possible output, b,
with (a, b) being in the relation.

The property of being a function, i.e., single-valued
```lean
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
```
When a relation is a function and is both injective
and surjective then the relation defines a pairing of
the elements of the two sets. Among other things, the
existence of a bijective relationship shows that the
domain and range sets are the same size.

```lean
-- The property of a relation being a many-to-one function
def isManyToOne {α β : Type} : Rel α β → Prop :=
  fun r => ¬isInjective r


-- The property of being a one-to-many injection
def isOneToMany {α β : Type} : Rel α β → Prop :=
  fun r => ¬isFunctional r ∧ isInjectiveRel r


-- The property of being a many-to-many relation
def isManyToMany {α β : Type} : Rel α β → Prop :=
  fun r => ¬isFunctional r ∧ ¬isInjectiveRel r


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
```

The property of a relation that relates every pair
of values one way or the other
```lean
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
```

## Examples


### Equality is an equivalence relation.


To show that that equality on a type, α, (@Eq α), is
an equivalence relation, we have to show that it's
reflexive, symmetric, and transitive. We'll give the
proof in a bottom up style, first proving each of the
conjuncts, then composing them into a proof of the
overall conjecture.

```lean
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
```

### The Property of Being Empty

Any emptyRel (see our definition) has the property of being empty.
```lean
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
```


### The Set.subset Relation is a Partial Order

```lean
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
```

### The inverse of an injective function is a function

```lean
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
```
