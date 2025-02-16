```lean
import DMT1.Lectures.L08_setsRelationsFunctions.«03_propertiesOfRelations»

namespace DMT1.Lectures.setsRelationsFunctions.homeworksSetsRelations

open DMT1.Lectures.setsRelationsFunctions.propertiesOfRelations
```

Homework #8 Properties of Relations.

<!-- toc -->


You must be able to do this homework on your own.
If getting to that point requires collaboration, you
may collaborate with up to two other people. In this
case, you are to hand in one assignment with the names
and email addresses of all the collaborators. Each
collaborator must work with every other one on this
assignment. You may not just split the problems one
or two for each person.

We've importd all of the definitions of properties of relations
from L03_properties_of_relations so you can use them here with no
problem. Use View > Editor Layout > Split Down to have two panes
open, one looking at the property definitions file and one open
on this one.

PROBLEM #1 [25 points]. We've see that, in Lean, every function
of type α → β is total. Any such function in Lean must be defined
*for all* values of the intput type, α. If you fail to provide an
output value for every input, Lean will tell you you're "missing
cases."

We can turn any function, f, in Lean into a binary relation by
specifying it membership predicate to be fun a b => b = f a. In
other words, (a, b) is in the relation exactly when b = f a. We
can now define a function that takes any function from any type,
α to any type β, and that returns the corresponding relation with
exactly this membership predicate.

```lean
def funToRel { α β : Type} : (f : α → β) → Rel α β :=
  fun f => fun a b => f a = b
```

Now we can propose, and prove, that every relation that is
obtained from any function has the property of being total
as defined by our isTotal predicate on binary relations. We
give a good amount of the proof in English, and a little bit
of it in Lean. You finish the missing formal parts.
```lean
example {α β : Type} (f : α → β) : isTotal (funToRel f) :=
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

example : ¬isSingleValued acctsOf :=
-- assume acctsOf is single valued:
fun (h : isSingleValued acctsOf) =>
-- show that that implies that 1 = 2
-- that's absurd so conclude ¬isSingleValued acctsOf
(
  -- ∀ x y z, r x y → r x z → y = z
  let a1 : acctsOf "Mary" 1 := Or.inl ⟨ rfl, rfl ⟩
  let a2 : acctsOf "Mary" 2 := Or.inr (Or.inl ⟨ rfl, rfl ⟩)
  -- TODO
  let contra := h _ _ _ _ _
  _
)
```

PROBLEM #3 [25 points]

State formally and prove the proposition that the
successor relation on natural numbers (Nat.succ) is
an injective function. You can use funToRel applied
to Nat.succ to define that relation if you want.

```lean
def succRel := funToRel Nat.succ

#reduce (types:=true) succRel 1 2
-- reduces to the proposition Nat.succ 1 = 2, i.e., 2 = 2

example : succRel 1 2 := rfl

-- HERE
example : isInjective succRel :=
And.intro
  -- succRel is a singleValued relation (a function)
  (fun a b c hab hac =>
    -- note that hab and hac are proofs of Nat.succ a = b and Nat.succ a = c
    -- rewrite goal from b = c to a.succ = b.succ hab and hac (right to left)
    -- that leaves a.succ = a.succ, which rw proves by the reflexivity of =
    by rw [←hab, ←hac]    -- the ← means rewrite right hand in goal with left
  )
  -- succRel is an injective relation
  (_)   -- ok, you have to prove the rest
```


PROBLEM #4 [25 points]

A. Given (non-zero) natural numbers a, b, and n, we
say that a is congruent to b mod n if a mod n = b mod n.
Complete the following definition of the binary relation,
congruence mod n.

```lean
def congruentModN (n : Nat) : Rel Nat Nat := fun a b => sorry

-- Test cases will succeed when you give the right definition
example : congruentModN 4 8 12 := rfl
example : congruentModN 5 25 50 := rfl
example : ¬congruentModN 4 4 9 := fun h => nomatch h
```


Now prove the proposition that congruence mod n is an equivalence relation
```lean
example (n : Nat) : @isEquivalence Nat Nat (congruentModN n) :=
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
