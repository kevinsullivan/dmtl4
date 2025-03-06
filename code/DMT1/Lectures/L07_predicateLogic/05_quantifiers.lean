/- @@@ Quantifiers

<!-- toc -->

TEMPORARILY UNDER CONSTRUCTION

Suppose:

- α is any type (such as Nat or A ∨ B)
- Pr : α → Prop is predicate expressing a property of α values (e.g., evennness)
@@@ -/

universe u
axiom α : Sort u      -- α can be in Prop (Sort 0), Type (Sort 1), or Type 1, 2, ...
axiom Pr : α → Prop

/- @@@

Then in predicate logic we also have two forms of quantifier expressions

- ∀ (a : α), Pr a
- ∃ (a : α), Pr a
@@@ -/


#check ∀ (a : α), Pr a    -- this is a proposition
#check ∃ (a : α), Pr a    -- this is a proposition


/- @@@

## Universal Quantifier: ∀ (a : α), Pr a

Here we have the form of a "universally quantified" proposition. It can be pronounced
and is to be understood as asserting that "*every* (a : α) satisfies Pr", or "Pr is true
of every  (a : α)", or "every (a : α) has property Pr", or "for any a there's a proof
of (rP a)", or just "for all a, Pr a".

### Introduction

To prove that every (a : α) has property Pr it will suffice to show that there'ss a way
to turn any such (a : α) into a proof of Pr a. In constructive logic, this is a job for
a function. If α is any type (including Prop), a proof of ∀ (a : α), Pr a, is a function,
pf : (a : α) → Pr a. That is the type of a function that takes any argument of type α and
that returns proofs the corresponding propositions Pr a, one proposition/type for each a.
That's it! It's the same as for any implication.
@@@ -/

def pf : ∀ (a : α), Pr a := (fun (a : α) => sorry)

/- @@@
Now to use a proof of an implication, apply it, as a function to any value (b : α) to
get a proof of Pr b.
@@@ -/

axiom b : α

#check pf b

/- @@@
We can call constructing a proof of (∀ a, Pr a) a universal generalization. We can
call the application of a generliation to a value to get a value-specific proof
universal specialization.
@@@ -/


/- @@@
## Existential Quantifier: ∃ (a : α), P a

Now we meet the form of an "existentially quantified" proposition. It can be read as
saying "there exists an a with property P", or "some a satisfies the predicate P."

### Introduction

To prove it, apply Exists.intro to some value (a : α) and to a proof (pf : P a).
@@@ -/

def aPf : ∃ (x : α), Pr x := Exists.intro b sorry   -- you also need a proof of P b

/- @@@
### Elimination

The rule for using a proof of existence is a little strange. If you have one,
you cannot ask for the value of the thing that exists, all you can get is that
is one *and you can give it a name* and along with you, finally, you get a proof
that that named thing satisfies the predicate. Those are the new ingredients you
can use in subsequent steps of reasoning.

Here's an example. We give most of a proof of a trivial proposition
that let's us assume a proof of an existentially qualitified proposition
so that we see how to use one. In this example we could of course just
ignore the proof argument and just return True.intro. The point, rather,.
is to see how to use Exists.elim *and what it does*. The key point here
is to see, by hovering over the remaining hole, that applying the elim
rule has given you two new context elements to work with: (1) *some* value,
(a : α), and a proof that that value, a, satisfies the predicate, Pr. In
a more interesting proof, you would then use these elements to help build
the proof you seek (here of True.intro).
@@@ -/

example : (∃ (x : α), Pr x) → True :=
  fun h =>
    Exists.elim
      h
      (
        fun a =>
          fun pra => _
      )

/- @@@
## A few examples
@@@ -/

example : ∃ (n : Nat), n = 0 := Exists.intro 0 rfl

example : ∀ (n : Nat), n + 1 ≠ 0
| _ => (fun c => nomatch c)

example : ∃ (n : Nat), n ≠ 0 :=
  Exists.intro 1 (fun c => nomatch c)

axiom Ball : Type
axiom Red : Ball → Prop
axiom Hard : Ball → Prop

#check Exists.elim

/- @@@
Exists.elim.{u} {α : Sort u} {p : α → Prop} {b : Prop} (h₁ : ∃ x, p x) (h₂ : ∀ (a : α), p a → b) : b
@@@ -/

example : (∃ (b : Ball), Red b ∧ Hard b) → (∃ (b : Ball), Red b) := by
  intro h
  apply Exists.elim h _
  intro b
  intro rh
  apply Exists.intro b rh.left
