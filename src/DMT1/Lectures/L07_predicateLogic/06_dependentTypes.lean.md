```lean
import Mathlib.Util.Delaborators
```


This section should be left as an option for interested
students in DMT1. It can be included in an introductory
graduate course or late undergraduate elective.

<!-- toc -->

# Dependent Types

Lean implements the logic of dependent type theory. The
key idea in dependent type theory is that the *type* of
one term can depend on the *value* of another type.

## Example and Discussion

A good example of a dependent type in Lean 4 is called
*Vector*. It's type is *Vector.{u} (α : Type u) (n : Nat) :
Type u*. For any element type, *α*, and any natural number,
*n*, *Vector α n* is the *type* of arrays (of *α* values)
*of length n*. The *type* depends on the *value* of *n*.
*** -/

#check Vector String 2    -- A type
#check Vector String 5    -- A different type

```lean
It's important to distinguish between merely polymorphic
types, on one hand, and dependent types, on the other. In
Lean, *Array α* is a polymorphic type (builder) but it is
not a dependent type. Parametrically polymorphic (generic)
types depend on other *types* but not on *values* of other
types.
```

#check Array String       -- a type
#check Array Nat          -- a different type
#check Array Bool         -- yet another type

```lean
Dependent types are different. They give rise to a distinct type
for each *value* of some other type. In the following examples,
we fix *α = String* but let the length vary, giving rise to a new
type for each possible natural number *value* of *n*.
```

#check Vector String 2  -- a type
#check Vector String 4  -- a different type
#check Vector Nat 4     -- yet another type

```lean
Dependent types vastly increase the expressiveness of a logic
such as that of Lean 4, enabling complex specifications to be
represented as types. Among other things, they are at the heart
of Lean's formalization of the *∀* and *∃* quantifiers in Lean,
which correspond directly to what we call *dependent function
types* and *dependent pair types*, as we now explain.
```

/- ***
## Dependently Typed Function Types

To see that you've already been using dependent types, just
consider an example of a universally quantified proposition.
Consider the proposition, *every person is mortal*.

### Every Person is Mortal

To start, we introduce the *variable* keyword in Lean. We can use
it to declare variables in one place that can then be used in multiple
subsequent definitions with no need for explicit declarations in each
individual case.

```lean
variable
  (Person : Type)
  (Mortal : Person → Prop)
```

With that, we can now formalize the proposition that every person
is mortal.

```lean
#check ∀ (p : Person), Mortal p
```

We've seen that a proof term for such a proposition will be a
function definition of this type. Here's a proof skeleton that
makes the point clear again.

```lean
example : ∀ (p : Person), Mortal p :=
  fun (p : Person)  =>  -- assume p is an arbitrary person
  _                     -- show that this person is mortal
```

Such a function takes any person, *p*, as an argument, and
(if the proof were complete) returns a proof of *Mortal p*.
The key point is that this return type, *Mortal p*, depends
on the *value, p*.

The core logic of Lean 4 supports the definition of dependent
function types. Dependent function types enable one to express
universal generalizations (∀ propositions) in Lean 4. As we see
in the example, if *A* is any type and *P : A → Prop* is any
predicate on *A*, then *∀ (a : A), P a* is the dependent type
of a *function* that takes any value *a : A* as an argument and
that returns a proof (a value of type) *P a* as a result.

Ordinary (non-dependent) function types in Lean are just special cases
of dependent function types where the return type isn't defined in term
of the argument value at all. The following types are thus equivalent:
*∀ (n : Nat), Nat*, and *Nat → Nat*. The latter notation is preferred
for non-dependent function types. See how Lean reports each type. Lean
even warns that the argument values are unused, which is to say the
return type (Nat) doesn't *depend* on the argument value.

```lean
#check ∀ (n : Nat), Nat
#check Nat → Nat
```


## Dependent Pairs (Sigma/Σ-Types)

Sigma types (Σ types) represent dependent pair types: a type of pair where
the type of the second component in a pair depends on the value of the first.
Among other things, a proof of an *existentially quantified* propositions in
Lean is a value of a dependent pair type. The first element of such a pair is
a natural number, *n*, and the second is a proof that *that particular n* is
even. The type of the second element, *Ev n*, thus depends on the value of the
first element of the pair.

```lean
-- Here's a simple definition of our evennness predicate
def Ev (n : Nat) : Prop := n % 2 = 0
example : ∃ n, Ev n := ⟨ 0, rfl ⟩
```

As another example, the *Vector α n* type in Lean is a type of dependent
pair values, where the first element of such a pair is a value of type,
*Vector α*, and the second element is a proof that that particular Vector
value has length *n*.

```lean
#check Vector
```

The Vector type incorporates an *Array* element by inheritance and then
adds the second element as a new field.

structure Vector (α : Type u) (n : Nat) extends Array α where
  size_toArray : toArray.size = n

As a final example, suppose we want to have a type of lists of α values
of some specific length, say 5. We can define such a type as what in Lean
is called a subtype, and it will be a type of dependent pairs, where the
first element is a list and the second element is a proof that *that* list
has length 5. Here's the notation.

```lean
def List5 (α : Type) : Type := { l : List α // l.length = 5}
example : List5 Nat := ⟨ [1,2,3,4,5], rfl ⟩
```

It's easy to check that if a list isn't of length 5, it cannot be used
to construct a value of the List5 type, because there will be no way to
construct the required second element of such a dependent pair.

```lean
example : List5 Nat := ⟨ [1,2,3,4], rfl ⟩
```
