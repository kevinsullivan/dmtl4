```lean
import Mathlib.Data.Rel
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Real.Basic

namespace DMT1.Lectures.setsRelationsFunctions.equality
```

# The Equality Relation in Lean (Eq)

<!-- toc -->


Equality is a binary relation. When we write, *a = b*, we
are asserting that the terms, *a* and *b*, refer to exactly
the same value.

In Lean, *Eq* is a binary relation on two values of any
single type, α that is used to expres propositions that two
values are equal. The term, *Eq a b*, is such a proposition.
We would ordinarily write it as *a = b*. Lean does provide
*=* as an infix operator for *Eq*.

```lean
#check Eq 1 "foo"   -- equality undefined on different types
#check Eq 1 2       -- the proposition, 1 = 2
#check 1 = 2        -- the same proposition infix = notation
#check "hi" = "hi"  -- an equality proposition that is true
```

## Formal Definition
The family of equality propositions in Lean is defined by the
polymorphic *Eq* inductive type. Applying it to any two values,
*a* and *b* of any one type, *α*, forms the proposition *a = b*.
Here's the formal definition.

```lean
inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a
```
### Introduction

To prove an equality proposition, one must apply the constructor,
*Eq.refl* to a *single* value, *a*, effectively yielding a proof
that *a = a*. No other equalities can be proved, except that terms
are reduced when comparing them for equality.

```lean
example : 1 = 1 := Eq.refl 1      -- both sides identical terms
example : 1 + 1 = 2 := Eq.refl 2  -- both sides reduce to 2
example : "Hello, Lean" = "Hello, " ++ "Lean" :=  -- same here
  Eq.refl "Hello, Lean"
```

### Elimination
The elimination rule (derived from the recursor for Eq) basically
says that if you have a proof, *heq*, of the equality, *a = b*,
and you have a proof, *pa* of the proposition, *P a* (*P* being a
predicate), then you can derive a proof of *P b* by applying the
elimination rule for equality, called *Eq.subst* to *heq* and *pa*,
as in the expression, `Eq.subst heq pa`*. The result will be a term,
*(pb : P b)*.

```lean
variable
  (α : Type)
  (a b c : α)
  (P : α → Prop)
  (heq : a = b)
  (pa : P a)

#check ((Eq.subst heq pa) : P b)
```

## Rewriting Using Equalities

There is little more natural than the idea that if we have a valid
argument using some term, *a*, and we also know that *a = b*, then
that same argument with *a* replaced by *b* will still be valid. In
other words, equalities allow us to *rewrite* any *a* to *b* as long
as we have and use a proof of *a = b*.

One can apply the *Eq.subst* inference rule directly, but it is more
common to use Lean's *rewrite* tactics, namely *rw* and *←rw*. Given
*heq : a = b*, the *rw* tactic rewrites *a* to *b*, while the *←rw*
tactic rewrites all *b* to *a*.

```lean
example
  (α : Type)      -- Suppose α is any type,
  (P : α → Prop)  -- P is any property of α values,
  (a b : α)       -- a and be are α values
  (heq : a = b)   -- a = b
  (ha : P a) :    -- and a has property P
  P b :=          -- Then so does b
Eq.subst heq ha   -- By rewriting a to b justified by a = b


example
  (Person : Type)           -- Suppose there are people,
  (Happy : Person → Prop)   -- who can be Happy, and
  (a b : Person)            -- that a and b are people
  (heq : a = b)             -- and moreover a = b
  (ha : Happy a) :          -- and finally that a is Happy
  Happy b :=                -- then b must also be happy
Eq.subst heq ha             -- by rewriting a to b using a = b
```

Naturally, Lean provides a tactic to automate the application
of the elimination rule for equality to convert proofs of *P a*
to proofs of *P b* using a proof of *a = b*. It's called *rewrite*
and is abbreviated *rw*. In comes in two flavors as the following
examples show.

```lean
example
  (Person : Type)           -- Suppose there are people,
  (Happy : Person → Prop)   -- who can be Happy, and
  (a b : Person)            -- that a and b are people
  (heq : b = a)             -- and moreover a = b
  (ha : Happy a) :          -- and finally that a is Happy
  Happy b :=
  by
    rw [heq]
    exact ha
    -- assumption (looks for a proof in your context)

example
  (Person : Type)           -- Suppose there are people,
  (Happy : Person → Prop)   -- who can be Happy, and
  (a b : Person)            -- that a and b are people
  (heq : a = b)             -- and moreover a = b
  (ha : Happy a) :          -- and finally that a is Happy
  Happy b :=
  by
    rw [←heq]
    exact ha
```

## Properties of Equality

From just the introduction and elimination rule, we can also prove
that the equality relation is reflexive (the introduction rule gives
us this), symmetric, and transitive; and having all three properties
also makes it into what we call an equivalence relation.

#### Reflexive

The introduction rule for equality assures that equality is what a
*reflexive* relation: every value of any type is related (equal) to
itself under this relation.


```lean
theorem eqRefl
  {α : Type}      -- given any type
  (a : α) :       -- and any value a
  a = a :=        -- a is related to itself
Eq.refl a         -- by the intro rule
```

In effect, the Eq.refl constructor is a proof of the
reflexivity of equality. It stipulates that for *any*
value, *a*, of any type, *α*, *a = a*.

```lean
#check @Eq.refl
```
```lean
Eq.refl :
  ∀ {α : Sort u_1}
    (a : α),
  a = a
```

#### Symmetric

A binary relation on a single type is symmetric if whenever
it relates any a to some b it also relates that b to that a.
It's easy now to prove as a theorem the claim that equality
as defined here is a symmetric relation.

```lean
theorem eqSymm {α : Type} (a b : α) : a = b → b = a :=
  by
    intro heq   -- assume a = b
    rw [heq]    -- rewrites goal b = a to a = a
                -- rw automates applying Eq.intro at the end
```

Lean provides a proof of the symmetry of equality. It's called
Eq.symm.

```lean
#check @Eq.symm
```

```lean
@Eq.symm :
  ∀ {α : Sort u_1}
    {a b : α},
  a = b → b = a
```

#### Transitive

A binary relation on a set is said to be transitive if, whenever
it relates some a to some b, and some b to some c, it relates a to
c. Again using just the introduction and elimination rules it's easy
to prove that equality as defined is a transitive relation.

```lean
theorem eqTrans {α : Type} (a b c : α) : a = b → b = c → a = c :=
by
  intro hab hbc   -- assume a = b and b = c
  rw [hab, hbc]   -- proof: rewrite twice then (auto) Eq.intro
```

Lean provides a proof of the transitivity of equality.
It's called Eq.trans.

```lean
#check @Eq.trans
```

```lean
@Eq.trans :
  ∀ {α : Sort u_1}
  {a b c : α},
a = b → b = c → a = c
```


#### Equivalence

Finally, if a relation is reflexive, symmetric, and transitive, we
call it an equivalence relation. Such a relation has the effect of
partitioning its domain into non-overlapping (disjoint) collections
of equivalent values called equivalence classes. Equality is clearly
an equivalence relation, partitioning terms into disjoint classes of
terms where all terms in the same class reduce to the same value (e.g.,
2, 1 + 1, 2 + 0, 2 * 1, etc). We will address equivalence relations in
more detail in the next chapter.

```lean
end DMT1.Lectures.setsRelationsFunctions.equality
```
