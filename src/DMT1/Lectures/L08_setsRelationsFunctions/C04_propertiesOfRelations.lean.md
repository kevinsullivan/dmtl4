```lean
import Mathlib.Data.Rel
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Real.Basic

namespace DMT1.Lectures.setsRelationsFunctions.propertiesOfRelations
```

# Properties of Binary Relations

<!-- toc -->

There are many important properties of relations. In this
section we'll formally define some of the most important.

## Some General Properties of Binary Relations

### Empty Relation

We start with the simple property of a relation being *empty*.
That is, no value pairs satisfy its membership predicate. We
would typically write the definition of such a property of a
relation as follows:

```lean
def isEmpty'' {α β : Type u} : Rel α β → Prop :=
  fun r => ¬∃ (x : α) (y : β), r x y
```

Here *α* and *β* are arbitrary types. We formalize the property
as a predicate on binary relations from *α* to *β*, having the
type, *Rel α β → Prop*. The definition is thus in the form of a
function from a binary relation, *r*, to a specific proposition
about it: that no values, *x* and *y*, satisfy its membership
predicate.

In this chapter, we will specify many properties of relations in
this style. To avoid having to introduce *α*, *β*, and *r* in each
case, we can declare them once using Lean's *variable* construct.
Lean will thereafter introduce them automatically into definitions
in which these identifiers are used. We will also define *e* as a
binary relation from a single type, *α*, to itself. A relation of
this kind is called *homogeneous*, or an *endorelation*. We will
use the identifier *e* for any endorelation.

```lean
section properties

variable
  {α β : Type u}  -- arbitrary types as implicit parameters
  (r : Rel α β)   -- arbitrary binary relation from α to β
  (e : Rel α α)  -- arbitrary homogeneous/endo relation on α
```

With these variable definitions, we can now specific the same
property with a lot less syntactic boilerplate. First, we can
omit declarations for *α*, *β*, and *r*.

```lean
def isEmpty' :=
  ¬∃ (x : α) (y : β), r x y
```

Second, Lean can infer the specified value is a proposition,
so we can omit the *: Prop* type declaration as well, leaving
us with pretty much what one would say in English: a relation
is empty if there isn't any pair, (x, y), in the relation.

```lean
def isEmpty := ¬∃ (x : α) (y : β), r x y
```

We will avail ourselves of the use of this shorthand for the
rest of this file. Just remember that the mere appearance of
the identifiers, *α, β, r,* or *e* in such a definition causes
Lean to insert type declarations for them, producing the same
desugared term as in the first version of *isEmpty* above.


### Complete Relation

The property of a relation relating every pair of values.
We call such a relation *complete*. NOTE: We've corrected
the previous chapter, which used the term *total* for such
a relation. Use *complete* as we will define *total* to be
a different property.
```lean
def isComplete := ∀ x y, r x y

-- Example, the complete relation on natural numbers
def natCompleteRel : Rel Nat Nat := fun _ _ => True

-- A proposition and a proof that it is complete
example : isComplete natCompleteRel :=
```
By the definition of isComplete we need to prove that
every pair is in this relation. In other words, we need
to prove, *∀ (a b : Nat), natCompleteRel a b*. This is
a universally quantified proposition, so we apply the
rule for ∀, which is to assume arbitrary values of the
arguments, *a,, b,* and then show *natCompleteRel a b*.
```lean
fun _ _ => True.intro
```


### Total Relation
A relation is said to be *total* if it relates every
value in its domain of definition to some output value.
In other words, a relation is total if its *domain* is
its entire *domain of definition*.
```lean
def isTotalRel := ∀ (x : α), ∃ (y : β), r x y
```


### Single-Valued Relation

A binary relation is said to be *single-valued* if no
input is related to more than one *output*. This is the
property that crucially distinguishes binary relations
in general from ones that are mathematical *functions.*
Simply put, a function cannot have more than one output
for any given input.

The way we express this property formally is slightly
indirect. It says that to be a function means that *if*
there areoutputs for a single input then they must be the
same output after all.
```lean
def isSingleValuedRel := ∀ x y z, r x y → r x z → y = z
```



### Surjective Relation

A relation is called *surjective* if it relates some
input to *every* output in its codomain. That is, for
every output, there is some input that *maps* to it.
We note that this property is often defined as being
applicable only to functions. We define *isSurjective*
below accordingly.
```lean
def isSurjectiveRel :Prop := ∀ (y : β), ∃ (x : α), r x y
```


### Injective Relation

A relation is said to be *injective* if there is no
more than one input that is related to any given output.
Such a relation is also called *one-to-one*, as distinct
from *many-to-one*, which injectivity prohibits.
```lean
def isInjectiveRel :=
  ∀ x y z, r x z → r y z → x = y
```


### Many-To-One Relation
A many-to-one relation is one that is not injective.
In other words, it's not the case that every input
maps to at most one output value.

```lean
def isManyToOneRel := ¬isInjectiveRel r
```

### One-To-Many Relation

A relation is said to be one to many if it allows
one input to map to multiple outputs while still
requiring that multiple inputs don't map to the same
output.

```lean
def isOneToMany :Prop :=
  ¬isSingleValuedRel r ∧
  isInjectiveRel r
```

### Many-To-Many Relation
A relation is said to be many to many if it is neither
functional (so some input maps to multiple outputs) not
injective (so multiple inputs map to some single output).

```lean
def isManyToMany :=
  ¬isSingleValuedRel r ∧
  ¬isInjectiveRel r
```



## Properties of Functions


### Function
We define an alias, *isFunction*, for the property
of being single-valued.
```lean
def isFunction : Rel α β → Prop :=
  isSingleValuedRel
```


### Total Function

A total function is a function that is total as a
relation, i.e., it maps every input to some output.

```lean
def isTotalFun := isFunction r ∧ isTotalRel r
```


### Injective Function

The term, injective, is usually applied only to
functions. This and the following few definitions
apply only to functions and thus all include as a
condition that *r* be function as well as, in this
case, never mapping one input to multiple outputs.
In other words, to be an injective function is to
be a function and to be injective as a relation.

```lean
def isInjectiveFun :  Prop :=
  isFunction r ∧
  isInjectiveRel r
```

*One to one* is another widely used name for being
injective, in contradistinction to being many-to-one.

```lean
def isOneToOneFun : Rel α β → Prop :=
  isInjectiveFun
```


### Surjective Function

Tbe be a surjective function is to be a function
(single-valued) and to be surjective as a relation.

```lean
def isSurjectiveFun :=
  isFunction r ∧
  isSurjectiveRel r
```


"Onto" is another name often used to mean surjective.
The idea is that the function maps its domain "onto
the entire codomain." A relation that maps its domain
to only part of the codomain can be said to map "into"
the codomain, but this use of the term is not standard.

```lean
def isOntoFun : Rel α β → Prop :=
  isSurjectiveFun
```


### Bijective Function

A *total* function is that is injective and surjective
is said to be *bijective*. Being bijective in this sense
means that (a) every input relates to exactly one output
(total), (b) every input maps to a different output (inj),
and (c) every output is mapped to by some input (surj).

From having a bijection between two sets one can conclude
that they must be of the same size, as in this case there
is a perfect matching of elements in one with elements of
the other.

```lean
def isBijectiveFun :=
  isTotalFun      r ∧
  isInjectiveFun  r ∧
  isSurjectiveFun r
```
When a relation is a function and is both injective
and surjective then the relation defines a pairing of
the elements of the two sets. Among other things, the
existence of a bijective relationship shows that the
domain and range sets are the same size.

## Properties of Endorelations

A binary relation, *e*, with the same set/type as both
its domain of definition and its co-domain is said to be
a *homogrneous* relation, and also an *endorelation*. We
are using the identifier, *e*, to refer to an arbitrary
endorelation. We now define certain important properties
of endorelations, in particular.


### Being Reflexive

A relation is reflexive if it relates *every*
value in the domain of definition to itself.


```lean
def isReflexiveRel  := ∀ (a : α), e a a
```


### Being Symmetric

```lean
-- The property, if (a, b) ∈ r then (b, a) ∈ r
def isSymmetricRel := ∀ (a b : α), e a b → e b a
```

Note that being symmetric do not imply that a relation
is total. There needs to be a pair, *(b, a)* in the
relation only if there's a pair *(a, b)*. Question:
Which of the following relations is symmetric?

- The empty relation
- { (1, 0), (1, 0), (2, 1) }
- { (1, 2), (1, 0), (1, 0), (2, 1) }

Give informal natural languages proofs in each case.


### Being Transitive

```lean
def isTransitiveRel := ∀ (a b c : α), e a b → e b c → e a c
```

Note that transitivity doesn't require totality either. Which
of the following relations are transitive?

- The empty relation
- The complete relation
- { (0, 1) }
- { (0, 1), (1, 2) }
- { (0, 1), (1, 2), (0, 2) }
- { (0, 1), (1, 2), (0, 2), (2, 0) }


### Equivalence Relation

```lean
-- The property of partitioning inputs into equivalence classes
def isEquivalence :=
  (isReflexiveRel e) ∧
  (isSymmetricRel e) ∧
  (isTransitiveRel e)
```


### Being Asymmetric

```lean
-- The property, if (a, b) ∈ r then (b, a) ∉ r
def isAsymmetricRel :=
  ∀ (a b : α), e a b → ¬e b a
```

What a commonly used arithmetic relation that's asymmetric?


### Being Antisymmetric

```lean
-- The property, if (a, b) ∈ r and (b, a) ∈ r then a = b
def isAntisymmetricRel :=
  ∀ (a b : α), e a b → e b a → a = b
```

What a commonly used arithmetic relation that's antisymmetric?


### Being Strongly Connected

A relation in which every pair of values is related
in at least one direction is said to be strongly connected.

```lean
def isStronglyConnectedRel := ∀ (a b : α), e a b ∨ e b a
```


## Ordering Relations

Orderings are a crucial class of relations.

### Partial Order

```lean
def isPartialOrder :=
    isReflexiveRel     e ∧
    isAntisymmetricRel e ∧
    isTransitiveRel    e
```

### Strict Partial Order


### Total Order

```lean
def isTotalOrder :=
    isPartialOrder      e ∧
    isStronglyConnectedRel e

def isLinearOrder : Rel α α → Prop := isTotalOrder
```


### Strict Total Order


### Preorder

A preorder is a relation that is Reflexive and Transitive.

Exercise: Write the formal definition and come up with a nice
example of a preorder.

### Well Order

<future>


## Closure Operations on Endorelations

### Reflexive Closure

Recall that for an endorelation, *e*, to be reflexive, *e*
must relate every value in its domain of definition to itself.

The reflexive closure of such a relation *e* is the smallest
relation that contains *e* (relates all of the pairs related
by *e*) and that also relates every value in the entire domain
of definition to itself.

We will give two definitions of this operation. The first is as
an inductive definition, and the second as a function that takes
any endorelation and returns the relation that is its reflexive
closure.

Here's the inductive definition, called *ReflClosure*. To use
it, you apply it to any endorelation, called *r* here, and you
get back a relation with two constructors for proving that any
given pair is in this relation. The first constructor assures
that every pair in *e* qualifies as a member. The second one
assures that for any *a*, *e a a* holds. That is, every pair of
a value with itself is in the reflexive closure.

```lean
inductive ReflClosure {α : Type u} (r : α → α → Prop) : α → α → Prop
| base  {a b : α} : r a b → ReflClosure r a b
| refl  (a : α)   : ReflClosure r a a
```


We can also define a reflexive closure function that, when
applied to any endorelation returns the relation (represented
as a membership predicate) that is its reflexive closure.

```lean
def reflexiveClosure' : Rel α α → Rel α α :=
  fun (e : Rel α α) (a b : α) => e a b ∨ a = b

def reflexiveClosure := fun (a b : α) => e a b ∨ a = b
```

### Symmetric Closure

Similarly, the *symmetric closure* of an endorelation, *e*,
is the smallest relation that contains *e* and has the fewest
additional pairs needed to make it symmetric. Note that if *e*
is empty, so is its symmetric closure, whereas the reflexive
closure of an empty relation having a domain of definition
that is not empty is never empty.

```lean
inductive SymmetricClosure {α : Type u} (r : α → α → Prop) : α → α → Prop
| base  {a b : α} : r a b → SymmetricClosure r a b
| flip  {a b : α} : r b a → SymmetricClosure r a b

def symmetricClosure {α : Type u} (r : α → α → Prop) : α → α → Prop :=
  fun a b => r a b ∨ r b a
```


### Transitive Closure

```lean
inductive TransitiveClosure {α : Type u} (r : α → α → Prop) : α → α → Prop
| base  {a b : α} : r a b → TransitiveClosure r a b
| step  {a b c : α} : TransitiveClosure r a b → TransitiveClosure r b c → TransitiveClosure r a c
```

A functional form of this definition, taking a relation and
returning its transitive closure, is more complicated, and not
worth the time it'd take to introduce it here.


### Reflexive Transitive Closure

It's often useful to deal with the reflexive and transitive closure
of an endorelation, *e*. This requires only the addition of a *refl*
constructor to the definition of transitive closure.

```lean
inductive ReflexiveTransitiveClosure {α : Type u} (r : α → α → Prop) : α → α → Prop
| base  {a b : α} : r a b → ReflexiveTransitiveClosure r a b
| refl  (a : α) : ReflexiveTransitiveClosure r a a
| step  {a b c : α} :
    ReflexiveTransitiveClosure r a b →
    ReflexiveTransitiveClosure r b c →
    ReflexiveTransitiveClosure r a c
```

As an interesting aside, first-order predicate logic is not
expressive enough to be able to express the claim that even a
specific relation is transitive, not to mention formalizing the
property of being transitive generalized over all relations.



Thus ends our section on properties of relations.
```lean
end properties
```


## Proving Properties of Relations

To prove that some relation, r, has some property P,
assert and and show that there is a proof of (P r).

As an example, let's assert and prove that equality
on the natural numbers is *total*. In other words,
we claim that there's a proof of the *proposition*,
*isTotal (@Eq Nat)*. Recall that the @ disables the
inference of implement arguments, here allowing the
type, Nat, to be given explicitly.

One of the first steps in getting to a proof of such
a proposition is to reduce the name of the property,
such as *isTotalRel*, to its definition, and in Lean
to its representation, as a logical predicate.

In an English language proof, you might say, "By
the definition of *isTotalRel*, it will suffice for
us to to show that *∀ x, ∃ y, r x y*." You then go
on to prove that more transparent form of the basic
proposition at hand.

In Lean it's the same. You can *unfold* (expand)
the definition of a term, such as *isTotalRel*, in
a larger expression using the *unfold* tactic.

```lean
example : isTotalRel (@Eq Nat) :=
  by
    unfold isTotalRel
    sorry     -- Exercise!
```


## Exercises

### A Reflexive Endorelation is Necessarily Total

```lean
example : isReflexiveRel e → isTotalRel e :=
by
  intro h
  unfold isReflexiveRel at h
  unfold isTotalRel
  intro a
  use a
  exact (h a)
```


### Equality is an Equivalence Relation.

To show that that equality on a type, α, (@Eq α), is
an equivalence relation, we have to show that it's
reflexive, symmetric, and transitive. We'll give the
proof in a bottom up style, first proving each of the
conjuncts, then composing them into a proof of the
overall conjecture.

```lean
-- equality is reflective
theorem eqIsRefl {α : Type}: isReflexiveRel (@Eq α) :=
  fun _ => rfl

-- equality is symmetric
theorem eqIsSymm : @isSymmetricRel α (@Eq α) :=
  -- prove that for any a, b, if a = b ∈ r then b = a
  -- use proof of a = b to rewrite a to b in b = a
  -- yielding b = b, which Lean then proves using rfl
  fun (a b : α) (hab : a = b) =>
    by rw [hab]


-- equality is transitive
theorem eqIsTrans : @isTransitiveRel α (@Eq α) :=
  -- similar to last proof
  fun (a b c : α) (hab : a = b) (hbc : b = c) =>
    by rw [hab, hbc]

-- equality is an equivalence relation
theorem eqIsEquiv {α β: Type}: @isEquivalence α (@Eq α) :=
  -- just need to prove that Eq is refl,, symm, and trans
  ⟨ eqIsRefl, ⟨ eqIsSymm, eqIsTrans ⟩ ⟩ -- And.intros
```


### The ⊆ Relation is a Partial Order

```lean
def subSetRel {α : Type} : Rel (Set α) (Set α) :=
  fun (s t : Set α) => s ⊆ t

#reduce @subSetRel
-- fun {α} s t => ∀ ⦃a : α⦄, a ∈ s → t a


example {α : Type}: (@isPartialOrder (Set α) (@subSetRel α))  :=
  And.intro
    -- @isReflexive α β r
    -- by the definition of isReflexive, show ∀ a, r a a
    (fun s =>               -- for any set
      fun a =>              -- for any a ∈ s
        fun ains => ains    -- a ∈ s
    )
    (
      And.intro
        -- @isAntisymmetric α β r
        -- ∀ (a b : α), r a b → r b a → a = b
        (
          fun (s1 s2 : Set α)
              (hab : subSetRel s1 s2)
              (hba : subSetRel s2 s1) =>
            (
              Set.ext   -- axiom: reduces s1 = s2 to bi-implication
              fun _ =>
                Iff.intro
                  (fun h => hab h)
                  (fun h => hba h)
            )
        )
        -- @isTransitive α β r
        -- ∀ (a b c : α), r a b → r b c → r a c
        (
          (
            fun _ _ _ hst htv =>
            (
              fun _ =>  -- for any member of a
                fun has =>
                  let hat := hst has
                  htv hat
            )
          )
        )
    )
```

### The Inverse of an Injective Function is a Function

```lean
#check Rel.inv
example : isInjectiveFun r → isFunction (r.inv) :=
  fun hinjr =>   -- assume r is injective
  -- show inverse is a function
  -- assume r output, r.inv input, elements c b a
  fun c b a =>
  -- we need to show that r.inv is single valued
  -- assume r.inv associatss c with both b and a
      fun rinvcb rinvca =>
        hinjr.right b a c rinvcb rinvca
```



## Homework

In this part of homework, we state and prove, as a theorem,
the proposition that, for any natural number, *n*, the *congruence
mod n* relation, on natural numbers, *a* and *b,* is an equivalence
relation. We formalize these ideas by defining *congModN (n : Nat)*
to be a *family of relations, one for each value of n*, each being a
(different) equivalence relation on the natural numbers. That's not
Lean, that's just the mathematics. The last detail, for a given *n*,
is to specify the relation membership predicate on pairs, *(a, b).*
Here, it will be that *1%n = b%n*.

```lean
def congModN (n : Nat) : Rel Nat Nat :=
                      -- for a given n
  fun a b =>          -- the binary predicate
    a % n = b % n     -- that defines (congModN n)
```



HOMEWORK PROBLEM #1: FINISH IT OFF.

To get further warmed up, let's prove a congruence
for some particular *n*. Let's make it *3*. So what
we expect is that *0, 3, 6, ...* will be congruent
mod n (mod 3). So will be *1, 4, 7, ...* And also
*2, 5, 8, ...*. We don't have to say *3, 6, 9,* as
they are just elements in the equivalence class for
0. So here we go: congruence mod 3 is an equivalence
relation.

### Congruence Mod 3 is an Equivalence Relation

```lean
example : isEquivalence (congModN 3) :=
by
  unfold isEquivalence
```
  By the definition of equivalence, we must show
  ```lean
    isReflexiveRel (congModN 3) ∧
    isSymmetricRel (congModN 3) ∧
    isTransitiveRel (congModN 3)
```lean
  constructor   -- applies first ∧ constructor
```

  On ∧.left we need a prove that (congModN 3) is reflexive
  And on the right, that it's symmetrical and transitive

```lean
  -- reflexive
  unfold isReflexiveRel
  intro n
  unfold congModN
  rfl

  -- split conjunction
  constructor

  -- symmetric
  unfold isSymmetricRel
  intro a b
  unfold congModN
  intro h
  rw [h]

  -- transitive

-- EXERCISE: fill this hole.
  sorry
```


### Congruence Mod n is an Equivalence Relation

Now we state and prove that for any n, conguence mod n is
an equivalence relation.

```lean
example : ∀ (n : Nat), isEquivalence (congModN n) :=
fun n =>
  And.intro
  (
    fun a =>
      rfl
  )
  (
    And.intro
    (
      fun a b h =>
        by
          simp [congModN] at h
          simp [congModN]
          rw [h]
    )
    (
      fun a b c hab hbc =>
        by
          simp [congModN] at hab
          simp [congModN] at hbc
          simp [congModN]
          rw [hab]
          assumption
    )
  )
```

### The Subset Relation is a Partial Order

```lean
theorem subsetPO (α : Type): isPartialOrder (@subSetRel α) :=
by
  unfold isPartialOrder
  apply And.intro
    (
      by
        unfold isReflexiveRel
        intro s
        unfold subSetRel
        intro t
        intro h
        assumption
    )
    (
      -- EXERCISE: Fill these holes.
      And.intro
        sorry
        sorry
    )
```

### Well Founded Relations






```lean
end DMT1.Lectures.setsRelationsFunctions.propertiesOfRelations
```
