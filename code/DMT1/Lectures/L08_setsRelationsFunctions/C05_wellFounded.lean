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

*UNDER CONSTRUCTION -- BROKEN -- NOTHING TO SEE HERE*

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

All that this says is that a term, *Acc e a*, is
a proposition. You can pronounce *Acc e a*, as *a*
is accessible under *e*. To see what that means, we
need to look at the definition.
@@@ -/

inductive Acc {α : Sort u} (r : α → α → Prop) : α → Prop where
  | intro (x : α) (h : (y : α) → r y x → Acc r y) : Acc r x

/- @@@
Previously we defined a predecessor *function*
by pattern matching on its argument and in the
case where it's zero, returning zero. We had to
return *something* for zero, and so chose *zero*,
making that function *total*.

Here by contrast we define Prec *logically*,not
*computationally*. This is how we define partial
functions in Lean: as relations. Here, we define
a *precedes* relation, *Prec*, that contains all
pairs of natural numbers, *(m, n)* where *m + 1*
equals *n*. The relation thus contains pairs such
as *(0, 1)*, which you can read as *0 precedes 1*.
Note that by this definition, *nothing* precedes
*0*.
@@@ -/

inductive Prec : Nat → Nat → Prop
| step : ∀ { m n }, m + 1 = n → Prec m n


set_option pp.showImplicit true

example : ∀ m, Prec m 1 → m = 0 :=
by
  intro m h
  cases h
  cases m
  rfl
  rename_i n a

/- @@@
Zero is accessible because it has no predecessor
@@@ -/
example : Acc Prec 0 :=
Acc.intro
  0
  (
    fun y h =>
      (
        nomatch h
      )
  )

/- @@@
One is accessible, because it can be reached only
by predecessors that are accessible. That's easy as
there's only one predecessor in this total order.
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
Given a relation, *r*, a value *(a : α)* is accessible
under *r* when

```
intro
  (x : α) (h : (y : α) → r y x → Acc r y) : Acc r x
```

 which it in turn will mean
that there are no infinitely paths starting from a*
with iterated application of *e* yielding ever smaller
values without end.

As a simple example, consider what we can call the
*predecessor* relation, *Pred*, on natural numbers.
We'll define *Pred m n* to be valid when *m + 1 = n*.
So *(0, 1), (1, 2), (2,3)* are good but not *(0, 2)*.
Note there can be no pair with a *0* second element.

So now what we want to mean when we say that a given
natural number, *a* is accessible under *Pred* is that
any path from *a* down by the iterated *application*,
as it were, of *e* must end after a finite number of
steps. What that would mean in turn is that *a* must
have been finitely constructed from starting values,
so is *accessible*, finitely constructible, from them.


Every natural number is accessible under what we can
call the predecessor relation, of all and only pairs,
*(m, n)* where *(m+1 = n)*, that is of pairs of one
number with its *successor*. Importantly, there is no
predecessor of *0* under this definition.

Now suppose we have some arbitrary (n : Nat). What we
want to mean by *Acc pred


This view interprets *r* as some kind of *is smaller
than* relation. So what *Acc r a* means in these terms
is that, starting from *a*, there is no way to *traverse
r* forever, always getting to even smaller terms. Rather,
what it means for *a* to be accessible is that every path
downwards from *a* ends after some finite interations, of
traversals through *r* to smaller terms.

So that's the usual semi-formal view from the top down.
But even better, let's look at it inductively *from base
cases on up by the iterated application of constructors of
larger terms.

We will make ideas concrete using as an example the
*predecessor relation*, a partial function on natural
numbers* that takes each natural number expect for *0*
to the number it is the successor of, and that is just
undefined for *0*.
@@@ -/

def prec : Rel Nat Nat := fun a b => a + 1 = b

-- Demonstration test cases
example : prec 0 0 := rfl -- yay, finally it's partial
example : prec 0 1 := rfl
example : prec 1 2 := rfl
example : prec 1 3 := rfl -- demonstration test failure

/- @@@
Here's a nice notation, and the same test cases again
@@@ -/
set_option quotPrecheck false
inductive Prec : Nat → Nat → Prop
| step : ∀ { m n }, m + 1 = n → Prec m n
-- m, n will be inferred from the Prec type

infix:50 "≺" => Prec

example : 2 ≺ 3 := Prec.step rfl  -- expect yes
example : 2 ≺ 4 := Prec.step rfl  -- expect no
example : 0 ≺ 0 := Prec.step rfl  -- yay, partial!


/- @@@
Ok, so there's our relation

As an aside, we see here both how, and the ease with
which, we can now represent *partial* functions in Lean:
not as function to compute with (which must be total in
our setting) but as declaratively specified *relations*
for *reasoning*.

To understand what it means for an endorelation to be well
founded, we need the notion of what it means for an element,
*(x : α)* to be *accessible* under a given relation, *r*.

Think of *r* as being some kind of *one smaller than* relation.
We will write *y is one smaller than x (under r)* as *r y x*.
One could call such a relation, *precedes*, and use an infix
notation, *y ≺ x*, to mean *y precedes x by one step under r*.

Now the question is whether the process of going from *x*,
through *r*, to *y*, `and then from *y* to an even smaller *z*
can be repeated forever. If so, then *x* is *not* accessible.
On the other hand, you are guaranteed eventually to hit some
*smallest* element, from which you can *descend* no further,
the *x* is said to be *accessible* (from that smallest value).

This notion will be crucial in establishing that it is okay,
(a) to use recursion down through the relation *r* as it will
terminate, or (b) that one is not inadvertently specifying an
infinite structure, as values of inductive types in Lean are
always finite by definition.

Here are two examples. First,  consider the predecessor relation
on the natural numbers. Every natural number, *a*, is accessible
under it, as you can only move from *a* down to its predecessor,
and from there further down, a finite number of times before you
reach zero and can go no further down. In other words, there is
*no infinite descending chain* from *x*. But on the other hand,
no number is accessible in the *integers*, because from any value
you can keep subtracting one forever, always with a new result.

Given any endorelation *r* on *α*, the property of a value,
*(x : a)*, being accessible is defined formally as follows.

```lean
inductive Acc {α : Sort u} (r : α → α → Prop) : α → Prop where
  | intro (x : α) (h : (y : α) → r y x → Acc r y) : Acc r x
```
Given the proposition that *x* is accessible under *r*, written
formally as *Acc r x*, it is valid, and a proof is obtained by
applying the *Acc.intro* (proof) constructor:

```lean
intro (x : α) (h : (y : α) → r y x → Acc r y) : Acc r x
```

What it says,reading from right to left, is that to prove
*Acc r x* it will suffice to apply *Acc.intro* to *x* and
to a proof, *h*, of the proposition that if any value, *y*,
that is one step smaller than *x* is accessible, then *x* is
too.  That makes sense because if such a *y* is accessible,
there can be no infinite descending chain from any such *y*,
and so any chain down from *x* must be finite, as well, being
just one *step* longer than a chain down from *y*. In sum, if
every value that is one step smaller than *x* is accessible,
then so is *x*.
@@@ -/

open Nat

-- 1. Define the "one-less-than" relation
def pred_rel (m n : ℕ) : Prop :=
  m = n + 1

-- 2. Prove accessibility for every n under pred_rel
def acc_pred_rel : (n : ℕ) → Acc pred_rel n
| 0 =>
  Acc.intro (fun (y : ℕ) (h : pred_rel y 0) =>
    -- pred_rel y 0 means y = 0 + 1 = 1, but 1 ≠ y in general
    -- we can use y = 1 and say "nomatch"
    nomatch h)
| (n + 1) =>
  let ih : Acc pred_rel n := acc_pred_rel n
  Acc.intro (fun (y : ℕ) (h : pred_rel y (n + 1)) =>
    -- h : y = n + 2, so we rewrite y to n + 2 and apply ih
    -- because pred_rel (n + 2) (n + 1), and we're going down to n
    match h.symm with
    | Eq.refl => ih)


def isWellOrder  {α  _ : Type} : Rel α α → Prop :=
  fun r => ∀ (s : Set α), s ≠ ∅ → ∃ m, (m ∈ s ∧ ¬∃ n ∈ s, r n m)



/- @@@
### The Predecessor Relation is Well Founded
@@@ -/

inductive PredRel : ℕ → ℕ → Prop
| step : ∀ {n : ℕ}, PredRel n (n + 1)

theorem predRel_wf : WellFounded PredRel :=
  WellFounded.intro (fun a =>
    Acc.intro a (fun y h =>
      match h with
      | step =>
        -- h : PredRel a y, and step : PredRel n (n + 1)
        -- So a = n, y = n + 1
        -- Then we recurse on n = a
        byexact Acc.intro a (fun z h' => nomatch h')))


#reduce (types := true) @isWellFoundedOrder Nat Nat predRel
-- ∀ (s : Set ℕ), s ≠ ∅ → ∃ m, m ∈ s ∧ ¬(∃ n ∈ s, predRel n m)
example : @isWellFoundedOrder Nat Nat predRel :=
  fun s =>
    fun nonempty =>
      -- ∃ m ∈ s, ¬∃ n ∈ s, predRel n m
      _

/- @@@
End of technical section
@@@ -/
end wellFounded

-- See [TPIL4](https://leanprover.github.io/theorem_proving_in_lean4/induction_and_recursion.html#well-founded-recursion-and-induction).

end DMT1.Lectures.setsRelationsFunctions.wellFounded
