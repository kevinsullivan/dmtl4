/- @@@
# Quantifiers: Universal Generalization (∀)

<!-- toc -->


Quantifiers are part of the syntax of predicate logic.
They allow one to assert that every object (∀) of some
type has some property, or that there exists (∃) (there is)
at least one (some) object of a given type with a specified
property. The syntax of such propositions is as follows:

- ∀ (x : T), P x
- ∃ (x : T), P x

The first proposition can be read as asserting that
every value *x* of type *T* satisfies predicate *P*.
Universal quantification is a generalized form of a
logical *and* operation: it is used to assert that
the first value of a type has some property, *and* so
does the second, *and* so does the third, through all
of them.

In this chapter we address universal generalizations
(∀ propositions). We cover existential quantification
in the next chapter.

## Introduction Rule (How to Prove ∀ (x : T), P)

In predicate logic, the way to prove *∀ (a : A), P a*
is to (1) *assume* that you've got an arbitrary value,
*a : A*, and then in that context, (2) give a proof of
*P a*. The reasoning is that if any arbitrary value *a*
satisfies *P* then every value of *a* must do so.

In Lean 4, a proof of a universal generalization has
exactly the same sense, and is presented as a *function:*
one that takes an arbitrary value, *(a : A)*, and that,
in that context constructs and returns a proof of *P a*.
The existence of such a function (which must be *total*
in Lean) shows that from *any* *a* one can construct a
proof of *P a*. That shows that every *a* satisfies *P*.
@@@ -/

/- @@@
### Example

Here's a trivial example. We assert that every natural
number, *n*, satisfies the proposition, *True*. This is
of course true, but let's see a proof of it.
@@@ -/

example : ∀ (n : ℕ), True :=
  fun n =>    -- assume an arbitrary n
  True.intro  -- show that that n satisfies True

/- @@@
So we see that the logical proposition, *∀ (n : Nat),
True*, is equivalent to the function type, Nat → True.
Given any natural number, *n*, such a function returns
a *proof* of (a value of type) True.
@@@ -/

#check ∀ (n : Nat), True  -- Literally Nat → True!

/- @@@
Here's yet another example: we define the natural number
squaring function, declaring its type using ∀ rather
than →. When we #check it's type, Lean reports it as
*Nat → Nat*, using its default notation, →, for this type.
@@@ -/

def square : ∀ (n : Nat), Nat := fun n => n^2
#check (square)   -- Nat → Nat
#reduce square 5  -- 25


/- @@@
Here's a logical example proving *∀ (f : False), False.
@@@ -/

def fimpf : ∀ (f : False), False := fun f => f
#check (fimpf)  -- a value/proof of type False → False

/- @@@
### Discussion
@@@ -/


#check Nat → False
example : Nat → False := fun n => _ -- stuck
example : ¬(Nat → False) :=
  fun (h : Nat → False) =>
    h 0


/- @@@
### Elimination Rule

Suppose you have a proof of *∀ (a : A), P a*. How do you use
it? The answer is that you *apply* it to a particular value,
*a : A), to get a proof of *P a*. The reasoning is that if
every value of type *A* satisfies *P*, then for any particular
value, *(a : A),* we should be able to obtain a proof of *P a*.
@@@ -/

variable
  (Person : Type)                     -- there are people
  (Mortal : Person → Prop)            -- property of being mortal
  (Socrates : Person)                 -- socrates is a person
  (AllAreMortal : ∀ (p : Person), Mortal p) -- all people mortal

-- We can now have a proof that socrates in particular is mortal
#check AllAreMortal Socrates

/- @@@
That brings us to the conclusion of this section
on universal generalization and specialization. Key
things to remember are as follows:

- Universal generalizations are function types
- Introduction: define a function of this type
- Elimination: Apply such a function to a particular
@@@ -/
