import Mathlib.Data.Rel
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Real.Basic

import DMT1.Lectures.L08_setsRelationsFunctions.C04_propertiesOfRelations

/- @@@
We've now imported the properties of relation defined in
propertiesOfRelations.
@@@ -/

namespace DMT1.Lectures.setsRelationsFunctions.wellFounded

/- @@@
# Well Founded Relations

<!-- toc -->

## For a Value to be Accessible Under an Endorelation

Suppose *e* is an endorelation on *(α : Rel α α)*, and
that *(a : α). We stipulate that what it means for *a*
to be *accessible* under *r*.

For now, let's view *r* as some kind of *smaller than*
relation. It's just a name. We can give it the concrete
notation to reflect this view.
@@@ -/

open DMT1.Lectures.setsRelationsFunctions.propertiesOfRelations

section wellFounded

variable
  (α : Type u)
  (e : Rel α α)

#reduce @Acc

/- @@@
```lean
Acc.{u}
  {α : Sort u}
  (r : α → α → Prop)
  (a✝ : α) :
Prop
```

We will say that a value, *x*, is accessible under an
endorelation, *r*, written as *Acc e a*, whenever every
value *y* that *precedes* *x* under *r* is accessible.
@@@ -/

inductive Acc {α : Sort u} (r : α → α → Prop) : α → Prop where
  | intro (x : α) (h : (y : α) → r y x → Acc r y) : Acc r x

/- @@@
### Accessibility under the Nat Precedes Relation

Previously we defined the predecessor relation on
natural numbers computationally, as a *function*
that takes any *Nat* and returns it's predecessor
(the number one less), except when the argument is
*0*, in which case, to be total, the function simply
returns *0* again.
@@@ -/


-- A computable, thus in type theory, total, function
def pred : Nat → Nat
| 0 => 0
| (n' + 1) => n'


/- @@@
### The Prec Relation (Immediately Precedes on Nats)
Now, with declaratively specified relations, we're
no longer constrained to define only total functions.
Here by contrast we define *Prec* to be the *partial*
function on natural numbers that takes every value to
its predecessor except for *0*, for which there simply
is no related predeessor value.

As you now know, it is very useful to have no cases, as
generalizations then hold trivially. This is what will
make it useful to have values for which there are no
predecessors at all, because they can then be the base
cases of objects that, trivially, have the property we
want all other values of a type also have. That will be
the property of accessibility of all natural numbers,
in this first instance, under the *Prec* relation.

We formally define the predecessor relation, called
*Prec* ("precedes"), as follows.
@@@ -/

inductive Prec : Nat → Nat → Prop
| step : ∀ { m n }, m + 1 = n → Prec m n


/- @@@

#### Prec 0 1

A pair is in this relation exactly when the first element,
*m*, is *one smaller* that the second, i.e., *m + 1 = n*.
When *m = 0* then *m + 1 = 1*, so *n = 1*. The pair with
the smallest first element is thus *(0, 1)*. We cabn read
this pair as stating *0 precedes 1* in the *Prec* relation.

As a quick example, let's prove that the pair, *(0, 1),*
is in this relation.
@@@ -/

example : Prec 0 1 := Prec.step rfl

/- @@@
EXERCISE: Prove that (1, 2) is in Prec.
EXERCISE: Prove (0, 2) is not.
@@@ -/



/- @@@
#### Prec m 1 => m = 0

If a natural number *m* precedes 1, it's 0.
@@@ -/

example : ∀ m, Prec m 1 → m = 0 :=
by
  intro m h
  cases h
  cases m
  -- case m = 0
  rfl
  -- case m is succ
  rename_i n a  -- annoy: make hiddens visible again
  nomatch a
  -- QED



/- @@@
### Zero is Accessible Under Prec

Zero is accessible under the precedes relation,'
because, as it has no predecessor at all, so it
satisfies that of its predecessors be accessible,
as there are none. By giving the proof a name we
can apply it as *zeroAcc* laterin this development.

EXERCISE: Grok this proof then express it in English.
HERE:
@@@ -/

theorem zeroAcc : Acc Prec 0 :=
Acc.intro
  0
  (
    fun  h _=>
      (
        nomatch h
      )
  )


/- @@@
### One is Accessible Under Prec

One is accessible, because it can be reached through
*r* from all of its predecessorss.  That's easy: we've
adready shown that there's only one predecessor of *1*
in this order; that's 0; and 0 is accessible trivially,
as is has no predecessors, so does has the property for
all of them.

EXERCISE: Complete the proof then express it all in English.
@@@ -/

example : Acc Prec 1 :=
Acc.intro
  1
  (
    fun y h =>
      (
        _
      )
  )

/- @@@
### Accessibility of a Value *a* Under Relation *r*

Given a relation, *r*, a value *(a : α)* is defined,
by the sinbgle *Acc* proof constructor, *Acc.intro*,
to be *accessible under r* just when every predecessor
of *a* is accessible under *r*.

```
intro
  (a : α) (h : (b : α) → r b a → Acc r b) : Acc r a
```

Taking apart this type, start by reading right to left.
To have a proof of *Acc r a* it will suffice (now read
left to right), for any value, *a*, to have a proof, *h*
that every predecessor, *b*, of *a* is accessible.

What this means is that there is no *path downward*
through the relation that can go on forever. That will
be the crucial idea

### Definition and Use of Infix Relation Notation

When talking about moving downwards, to ever smaller
terms, by iterative application of a relation, r, it
can be helpful to see the relation expressed in infix
notation using a symbol reminscent of *less than*. We
can use this symbol, *≺* and pronounce is as *precedes*.
@@@ -/


infix:50 "≺" => Prec

example : 0 ≺ 0 := Prec.step rfl  -- partiality!
example : 0 ≺ 1 := Prec.step rfl  -- expect yes
example : 2 ≺ 3 := Prec.step rfl  -- expect yes
example : 2 ≺ 4 := Prec.step rfl  -- expect no!!



/- @@@
### Every Natural Number is Accessible Under *Prec*

For a number, *a*, to be accessible under *Prec* thus
means that any path from *a* down by *applications* of
*Prec* to immediate predecessors will eventually reach
zero. At that point, a proof of accessibility, again,
is trivial, as it need only hold for all predecessors,
where, for zero, there are none. It's essential that we
have properly represented the predecesor function (now
as a specified relation) as a partial function. We are
relying on there being exactly no cases of predecessors
to consider for the base case of zero.
@@@ -/



/- @@@
## The Property of Relation Being Well Founded

EXERCISE: State and prove as a theorem that every
natural number is accessible under the Prec relation.
@@@ -/




end wellFounded

/- @@@
## Further Information

See [TPIL4](https://leanprover.github.io/theorem_proving_in_lean4/induction_and_recursion.html#well-founded-recursion-and-induction).

@@@ -/

end DMT1.Lectures.setsRelationsFunctions.wellFounded
