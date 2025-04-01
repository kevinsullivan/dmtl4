```lean
import DMT1.Lectures.L08_setsRelationsFunctions.«04_propertiesOfRelations»

namespace DMT1.Lectures.setsRelationsFunctions.homeworksSetsRelations

open DMT1.Lectures.setsRelationsFunctions.propertiesOfRelations
```

Homework #8 Properties of Relations.

<!-- toc -->

```lean
variable
  {α β : Type u}  -- arbitrary types as implicit parameters
  (r : Rel α β)   -- arbitrary binary relation from α to β
  (e : Rel α α)  -- arbitrary homogeneous/endo relation on α
```

## The Defined For Relation

We say a relation, *r : α → β*, is *defined* for an input,
*(a : α)* shdn there is some corresponding *(b : β)* such that
*a* and *b* are related by *r*. In this case we can also
say that *r* maps *a* (viewed as an input) to *b* (viewed
as an output).


```lean
def isDefinedFor (a : α) := ∃ x, r a x
```


Given any total function, f, represented by a lambda
expression in Lean, we can have it represented as a
binary relation, that represented as a binary predicate.
It's more complicated in the other direction.

```lean
def funToRel (f : α → β) : Rel α β :=  fun a b => f a = b
```

Now we can propose, and prove, that every relation that is
obtained from any function has the property of being total
as defined by our isTotal predicate on binary relations. We
give a good amount of the proof in English, and a little bit
of it in Lean. You finish the missing formal parts.


```lean
example (f : α → β) : isTotalRel (funToRel f) :=
```
by the definition of total, what is to be proved is that
∀ (x : α), ∃ (y : β), r x y. We first assume an arbitrary
input value a, then we show there exists a corresponding
output value such that the pair is in the relation. Just
a little thought produces (f a) as the witness, as it is
exactly the value that corresponds to the input, a. Then
we need to prove ((funToRel f) a (f a)). By the definition
of funToRel we need to show that (a, (f a)) is in the
relation but that requires exactly that the output, f a,
is equal to f applied to the input, a, i.e., f a = f a.
```lean
fun a =>
  Exists.intro
  (sorry)
  (sorry)
```


PROBLEM #2 [25 points]

We repeat here the definition of the bank account
number relation from the relations.lean file. Here
you are to state and prove the proposition that this
relation is not single-valued.

```lean
def acctsOf : Rel String Nat := fun s n =>
  s = "Mary" ∧ n = 1 ∨
  s = "Mary" ∧ n = 2 ∨
  s = "Lu"   ∧ n = 3

example : ¬isSingleValuedRel acctsOf :=
-- assume acctsOf is single valued:
fun (h : isSingleValuedRel acctsOf) =>
-- show that that implies that 1 = 2
-- that's absurd so conclude ¬isSingleValued acctsOf
(
  -- ∀ x y z, r x y → r x z → y = z
  let a1 : acctsOf "Mary" 1 := Or.inl ⟨ rfl, rfl ⟩
  let a2 : acctsOf "Mary" 2 := Or.inr (Or.inl ⟨ rfl, rfl ⟩)
  by
    unfold isSingleValuedRel at h
    let f : 1 = 2 := h "Mary" 1 2 a1 a2
    exact nomatch f
)
```

PROBLEM #3 [25 points]

The successor relation on the natural numbers maps
each natural number to its successor State formally and prove the proposition that the
successor relation on natural numbers (Nat.succ) is
an injective function. You can use funToRel applied
to Nat.succ to define that relation if you want.

```lean
def succRel := funToRel Nat.succ

example : succRel 1 2 := rfl

-- HERE
example : isInjectiveRel succRel :=
by
  unfold isInjectiveRel
  intro x y z h k
  unfold succRel at h
  unfold succRel at k
  unfold funToRel at h
  unfold funToRel at k
  rw [←h] at k
  -- What do you need to know to conclude x = y?
  apply Nat.succ.inj at k
  exact Eq.symm k
```


PROBLEM #4 [25 points]

A. Given (non-zero) natural numbers a, b, and n, we
say that a is congruent to b mod n if a mod n = b mod n.
Complete the following definition of the binary relation,
congruence mod n.

```lean
def congruentModN (n : Nat) : Rel Nat Nat := fun a b => a%n = b%n

-- Test cases will succeed when you give the right definition
example : congruentModN 4 8 12 := rfl
example : congruentModN 5 25 50 := rfl
example : ¬congruentModN 4 4 9 := fun h => nomatch h
```


Now prove the proposition that congruence mod n is an equivalence relation
```lean
example (n : Nat) : @isEquivalence Nat (congruentModN n) :=
```
By the definition of equivalence, what we need to show is that the
relation is reflexive, symmetric, and transitive.

```lean
And.intro
  -- It's reflexive
  (
    sorry
  )

  (
    And.intro
    -- It's symmetric
    (sorry)

    -- It's transitive
    (sorry)
  )
```

B. Next ... tbd

```lean
end DMT1.Lectures.setsRelationsFunctions.homeworksSetsRelations
```
