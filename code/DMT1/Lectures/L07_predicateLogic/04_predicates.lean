/- @@@
# Predicates

<!-- toc -->

In this chapter and from now on we'll be working with Lean's
standard embedding of predicate logic, which is what we just
covered in the last chapter, where propositions are encoded as
types of the Prop (rather than Type) sort. But let's start with
the question, what is a predicate?

## Parameterized (Generalized) Propositions

A predicate in any predicate logic is simply a parameterized
proposition. If *KisFromCville* and *CisFromCVille* are both
propositions, now represented by types of these names in Prop,
and if they both have the same general meaning for for different
particular people, then we can factor that variation by person
by making that person a parameter to a function that then returns
the final proposition with that particular person's name plugged
in.

As we see here, *generalizing* over all *people* let's us say
in just one place what forms of evidence we're willing to take
for *any* person in just one place. Note that here and from now
on will will represent logical, or reasoning, types in Prop.
@@@ -/

/- @@@
First, though, the mapping of related propositions to entirely
separate types:
@@@ -/

-- Specialized Proposition: Carter is from Charlottesville
inductive KevinIsFromCville : Prop where
| cvilleBirthCert
| cvilleDriversLicense
| cvilleUtilityBill

-- Specialized Proposition: Carter is from Charlottesville
inductive CarterIsFromCville : Prop where
| cvilleBirthCert
| cvilleDriversLicense
| cvilleUtilityBill

/- @@@
And now we can write our *generalized* predicate. We will
call it IsFromCharlottesville. It will be parameterized by
(generalized over) the possible values of a *Person* type,.
Here this will be the following ordinary data type. In this
example, it has just three values: Carter, Kevin, and Tammy.
@@@ -/

inductive Person : Type where | Carter | Kevin | Tammy
open Person

/- @@@
Now we're set to define PIsFromCville as a predicaate
on Person values represented as an inductive type that
is paramterized by a Person, and that when applied (or
specialized) to a particular Peron yields a proposition
about that Person.

On the first line, below, we specify the  name of the
predicate then a colon then its parameter, and finally
that the type that results from the application of the
predicate to a particular person is a type in Prop: it
represents the *proposition* that that person satisfies
whatever else the predicate might require.
@@@ -/


-- Generalization: proposition that <p> is from CVille
inductive PIsFromCville : Person → Prop where
| cvilleBirthCert       (p : Person) : PIsFromCville p
| cvilleDriversLicense  (p : Person) : PIsFromCville p
| cvilleUtilityBill     (p : Person) : PIsFromCville p
open PIsFromCville

-- Now we can *apply* this generalization to a particular person
#check PIsFromCville Kevin   -- specialization to particular proposition
#check PIsFromCville Carter  -- pronounce as "Carter is from Cville"
-- A predicate gives rise to a family of propositions (how many here?)

/- @@@
As we'e emphasized before, a predicate is a function
from arguments to propositions, where propositions are,
again, represented as *types* in *Prop*.
@@@ -/
#check PIsFromCville

/- @@@
## Proving Propositions Specialized from Predicates

Finally we can now see how to "prove" propositions derived from
predicates represented as "inductive type builders." You give
IsFromCville a Person, it gives you not only a proposition about
that person, but the rules for constructing proofs of *any* such
proposition. The following code declares KIFC and CIFC as proofs
of our two propositions, using the same proof/value constructors
in both cases, as they're common to *all* specializations of the
given predicate.
@@@ -/
def pfKevin : PIsFromCville Kevin := cvilleBirthCert Kevin
def pfCarter : PIsFromCville Carter := cvilleUtilityBill Carter

/- @@@
So there! We've now represented a *predicate* in Lean, not
as a type, per se, but as a function that takes a Person as
an argument, yields a proposition/type, and provies general
constructors "introduction rules" for contructing proofs of
these propositions.
@@@ -/

/- @@@
## The Property of The Evenness of Natural Numbers

As another example, we define a very different flavor of
predicate, one that applies not to people but the numbers,
and that indicates not where one is from but whether one is
even or not. This is an *indictive* definition, in Prop, of
the recursive notion of evenness. It's starts with 0 being
even as a given (constant constructor), and the includes an
indictive constructor that takes any number, *n*, and proof
that it is even and wraps it into a term that type checks as
a proof that *n+2* is even. Note that term term accepted as
a proof that *n+2* is even has embedded within it a proof
that *n* is even. These recursives structures always bottom
out after some finite number of steps with the proof that 0
is even. Note that we have Ev taking numbers to propositions
*in Prop.*
@@@ -/

inductive Ev : Nat → Prop where
| evZero : Ev 0
| evPlus2 : (n : Nat) → Ev n → Ev (n + 2)

open Ev

/- @@@
And here are some proofs of evenness
- 0 is even
- 2 is even
- 4 is even
- 6 is even (fully expanded)
@@@ -/

def pfZeroEv : Ev 0 := evZero
def pfTwoEv : Ev 2 := evPlus2 0 pfZeroEv
def pfFourEv : Ev 4 := evPlus2 2 pfTwoEv

-- hint: find the base proof then read this inside out
def pfSixEv : Ev 6 :=
  evPlus2
    (4)
    (evPlus2      -- proof that 4 is even
      (2)
      (evPlus2    -- proof that 2 is even
        (0)
        evZero    -- constant proof that 0 is even
      )
    )

/- @@@
Why can't we build a proof that 5 is even?
Well, to do that, we'd need a proof that 3
is even, and for that, a proof that 1 is even.
But we have no to construct such a proof. In
fact, we can even prove that an odd number (we
might as well just start with 1) is *not* even
in the sense defined by the *Ev* predicate.
@@@ -/

example : ¬Ev 1 :=
/- @@@
Recall: ¬Ev 1 is defined to be (Ev 1 → False).
To prove ¬Ev 1 we need a function of this type.
Applied to a proof Ev 1, it return a proof a False.
Read it out loud: *if* Ev 1 then False, with the
emphasis on if. But Ev 1 is not true, it's false,
so the entire implication is true as explained by
the fact that it's true for *all* proofs of Ev 1
(of which there are none).A  total function from
an uninhabited type to any other type is trivial.
Here, it's:
@@@ -/
fun (h : Ev 1) => nomatch h

/- @@@
Any proopsition quantified universally over an
empty set or type is valid, because it's true for
all values in that set or type, and because there
are none, in particular.

Another way to see that this makes sense is to view
universal quanitification as logical conjunction of
the family of propositions generated by the predicate
on the right specialized to a proposition about each
partixular value in the set or type.

The generalized conjunction of such a paramterized
family of propositions could be thought of as being
computed by recursion. With more than zero terms, you
take the conjunction of the first time with the result
of aplying this procedure to the rest. To preserve the
result when finally combining it with the answer in the
case where there are zero conjuncts to conjoin, the result
for the empty case has to be *true*. Yet another way to
see it: *true* is both a left and right identity element
for logical (truth-functional) *And*. You should check
your undertsanding by finishing this proof that True *is*
both a left and a right identity element for *And*.
@@@ -/

theorem leftRightIdentityAndTrue :
/-@@@
Note quantification over all propositions. So now we're
seeing that it makes eminent sense to express ideas at a
level of generality not expressible in first-order theory.
But here we have captured exactly the abstraction that we
want. You can finish the proof here that True really is an
identity, both left and right, for any proposition.
@@@ -/
∀ (P : Prop),
  ((P ∧ True) ↔ P) ∧
  ((True ∧ P) ↔ P)
:=
fun (p : Prop) =>
  And.intro
    (Iff.intro
      (fun h => h.left)
      (fun h => ⟨ h, True.intro⟩))
    (sorry)
