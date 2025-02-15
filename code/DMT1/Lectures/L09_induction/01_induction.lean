import Mathlib.Tactic.Ring

/- @@@
# Induction

<!-- toc -->


Suppose that you have some arbitrary type, α, and
that, for *any* value (t : α), you want produce a
corresponding output of some output type. Such an
output could be a data value, or it could be a proof
of some proposition, including one that depends on
any particular (t : α).

## Two Fundamental Applications of Induction Axioms

There are two cases want to consider.

In the first case, the output type, is some data
type, such as β = Nat. In the second case, it is
proposition, (P t), that in general depends on the
particular (t : α).

### Defining Computational Functions

In the first case, one wants to construct a function
of type α → β. We can also write this function type
as ∀ (a : α), β, emphasizing that a function in Lean
is necesarily total: defined for every (a : α).

### Defining Proofs of Universal Generalizations (∀)

In the second case, one wants to construct a proof
of a universal generalization: ∀ (a : α), P a, where
P is some predicate, P : α → Prop, on α values. As we
have learned, a proof of such a ∀ proposition also
has the form of a function, assuming an argument,
(a : α), and constructing and returning a proof of
the proposition (a value of the type), (P a).

### Every Inductive Type Has Elimination Axioms

In either case, and miraculously for *any* type, α,
an induction axiom, specific to that type, can help.
Indeed, every inductive type definition in Lean comes
with at least one inducation axiom specifically for
defining total functions and for proving universal
generalizations over values of that input type, α.
@@@ -/

/- @@@
## Definining Total Functions by Induction

As an easy example, suppose we want to define a total
function from Bool to Bool. As a concrete example, let
it be the negation function that we want: taking true
to false, and false to true.

You should recall the inductive definition of the Bool
type, but here it is again just in case:

inductive Bool : Type where
| true  : Bool
| false : Bool

To have a total function from Bool inputs, we *must*
define an output for each of the two constructors: an
output for true and an output for false. Our usual way
to do this is with some nice Lean syntax, as follows.
@@@ -/

-- Here's the syntax we've always used

def myNeg0 : Bool → Bool
| true => false
| false => true

/- @@@
Here's exactly the same definition using
an explicit match statement
@@@ -/

def myNeg1 : Bool → Bool :=
fun b =>
  match b with
  | true => false
  | false => true

/-
And now finally, here's how we can define this
function by applying an induction axiom for Bool.
In Lean, it's called Bool.rec.
@@@ -/

#check Bool.rec

/- @@@
Here we explain it in more detail.

Bool.rec.{u}
  {motive : Bool → Sort u}
  (false : motive false)
  (true : motive true)
  (t : Bool) :
  motive t

The *implicit* argument, motive, is the the function
(or proof of a ∀ proposition) that we seek. The {u}
is a universe level, also inferred. You don't need to
worry about it here.

The next two arguments are where we define the right
outputs for each of the constructors. This is where
again giving answers "by cases" just as before. So let
us see it in action.
@@@ -/


/- @@@
In this example we turn off implicit arguments using @
so that we can see all the arguments explicitly. First
we see that the following expression at least checks out
to be of type Bool → Bool. We use Lean syntax to clarify
which named arguments we're proving as arguments.
@@@ -/

#check (@Bool.rec
          (motive:=(λ (_ : Bool) => Bool))  -- type of function
          (false:=true)                     -- answer for false
          (true:=false))                    -- answer for true

/- @@@
This expression exactly reflects the case analysis that we
used in our first implementation of this function. Indeed,
Lean "desugars" the nice notation we've been using to just
this expression.
@@@ -/

-- When we apply this expression to an argument we get the right result
#reduce (@Bool.rec (motive := (λ (_ : Bool) => Bool)) true false) true
#reduce (@Bool.rec (motive := λ (_ : Bool) => Bool) true false) false

-- We can write test cases to confirm
example : (@Bool.rec (motive := (λ (_ : Bool) => Bool)) true false) false = true := rfl
example : (@Bool.rec (motive := (λ (_ : Bool) => Bool)) true false) true = false := rfl

/-
Lean doesn't fully support definition of computational functions using recursors.
It won't generate code for them. You're thus forced to use Lean's nicer syntax to
define computational functions.
@@@ -/

def myNeg : Bool → Bool := (Bool.recOn true false) -- oops

/- @@@
## Proving Universal Generalizations by Induction

Let's now define a simple property of Boolean values
and write and prove the propotion that every Boolean
has this property. The property that we will use here
is fun b => b ∧ false = false. We'll call it andFalse.
@@@ -/

def andFalse (b : Bool) := (b && false) = false

-- We could also have written it like this of course
def andFalse' := fun (b : Bool) => (b && false) = false

/- @@@
We can see that the andFalseIsFalse property is true
of every Boolean value, of which there are only two.
@@@ -/
#reduce (types:=true) andFalse true   -- false = false
#reduce (types:=true) andFalse false  -- false = false


/- @@@
Here's a formal statement in predicate logic of the claim
that andFalse b is true for all Boolean values, b. The
proofs is by simple case analysis. In each case what is
to be proved is false = false, and that's by reflexivity
of equality.
@@@ -/
def allFalseAnd : ∀ (b : Bool), andFalse b
| true => rfl
| false => rfl

/- @@@
And now for the punchline. Here's the same proof but now
given by explictly applying the induction axiom, Bool.rec.

The basic idea, again, is that we give it answers for each
of the constructors of the Bool type (as we just did but with
nice syntax).
@@@ -/

def allFalseAnd' : ∀ (b : Bool), andFalse b :=
  Bool.rec
    (motive := (λ (b: Bool) => andFalse b)) -- type of proof
    rfl                                     -- case for b = false
    rfl                                     -- case for b = true


/- @@@
## Induction on Natural Numbers

Let's look at the definition of the Nat type and then at the
induction axiom for natural numbers, Nat.rec. Here's the Nat
type definition. Unlike Bool, we now have a constructor that
not only takes an argument, n, but where the argument is of
the same type as the type being defined. This means that any
"larger" Nat will have a "one smaller" one as a component. We
build larger Nats from smaller ones.

inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

@@@ -/

#check Nat.rec

/-
Here's the induction principle/axiom

Nat.rec.{u}
  {motive : Nat → Sort u}
  (zero : motive Nat.zero)
  (succ : (n : Nat) → motive n → motive n.succ)
  (t : Nat) :
  motive t

The explanation is almost as before. Motive still
defines the type of function or proof that we want.
If we're defining the factorial function, for example,
motive n, for any n, will be Nat. If we're building
a proof of ∀ n, P n, where P is a predicate on Nat,
then the return type for n will be P n, which is to
say that the return value for n will be a proof that
that n satisfies the predicate (has the property), P.

Similarly, the last argument, t, is an eventual input
to the function being defined, with a result of type
(motive t) being returned at the end of the day.

### Defining Functions on Nat by Induction

Now comes the interesting part: the cases. In the first
case, for input zero, we just define the right Nat return
value. But the second argument required for induction is
a proof of the proposition that, "if you know n, and the
right answer for n, then you can have the answer for n+1."

Such a proof is a step function: if given n' and a the right
result for n', it computes and returns the result for n'+1.
In other words, just as we build a next bigger Nat from a
one-smaller one, so now we build the *result* of a desired
function for n'+1 from the one-smaller Nat, n', and from
the right result for n'.

There. We can now state how one defines a function, f, from
*any* natural number to a desired result, by providing (1)
the right answer for n = 0, and (2) a way to produce the right
answer for n > 0, where n = n' + 1, given n' and the result
for n'. The second argument here defines a function that if
given n' and the answer for n' computes the answer for n'+1.
@@@ -/

/- @@@
Suppose the function we want to define is factorial. Here
is the syntax we've been using all along
@@@ -/

def fact0 : Nat → Nat
| 0 => 1
| (Nat.succ n') => (Nat.succ n') * fact0 n'

example : fact0 0 = 1 := rfl
example : fact0 5 = 120 := rfl

/-
But as we now understand, this nice notation is
really using the induction axiom for the Nat type
internally. Here's the function definition now by
explicit application of induction, using Nat.rec.
@@@ -/

-- It has the right type! Nat → Nat
#check  (
  Nat.rec                                 -- apply induction
    (motive := (λ (_ : Nat) => Nat))      -- function to define
    (1)                                   -- answer for zero (n = 0)
    (fun n' factn' => (n' + 1) * factn')  -- answer for succ, given n' and answer for n'
)

-- And it computes the right results!
example : (
          Nat.rec
            (motive := (λ (_ : Nat) => Nat))
            (1)
            (fun n' factn' => (n' + 1) * factn')
        ) 0 = 1
        := rfl

example : (
          Nat.rec
            (motive := (λ (_ : Nat) => Nat))
            (1)
            (fun n' factn' => (n' + 1) * factn')
        ) 5 = 120
        := rfl

/- @@@
### Proof by Induction (on the Natural Numbers)

Induction can't be used to prove any proposition. It is
used to prove universal (∀) propositions. You can think
of it as a big machine that, if given the right parts,
gives you back a function from *any* value of the input
type to the correct output value. If that output value
is ordinary data, as it was for factorial, then by the
application of induction you've defined a nice function.
If the output value is a proof of (P n) for input n, then
you have proved that P holds for *all* n.

Let's see a classic example, first in English and then
in Lean.

The claim is that for all natural numbers n, the sum of
all the natural numbers up to an including n, which is
often written as (for i = 0 to n) Σ i, is always equal
to n * (n + 1) / 2.

To begin our exploration, let's define a simple function
to compute this sum. It's by recursion, of course.
@@@ -/

def sumToN : Nat → Nat
| Nat.zero  => 0
| (n' + 1) => sumToN n' + (n' + 1)

example : sumToN 0 = 0 := rfl
example : sumToN 5 = 15 := rfl
example : sumToN 10 = 55 := rfl

/-
Now we can formally define the property we will claim
every natural number has.
@@@ -/

def sumToNProp (n : Nat) := 2 * sumToN n = n * (n.succ)

/-
Next we can state the universal generalization we want.
@@@ -/

def sumToNPropAll := (∀ (n : Nat), sumToNProp n)

/-
And now we can prove it, by induction. For this we will
need to provide two "parts". The first is the correct value
for n = 0. In this case, sumToN 0 = 0, and n * (n + 1) is
also zero, so proof result that we want in this case is rfl.
@@@ -/
/-
The proof is by induction on the natural number n.

Base case: The answer for n = 0 is clearly 0. So the proof
we want for n = 0 is just a proof of 0 = 0, which we can have
by the reflexivity of equality.
@@@ -/

-- Base case (for n constructed by Nat.zero)
def sumZero : 0 = 0 := Eq.refl 0

-- Inductive case (for n constructed by Nat.succ)
/-
What we need to prove here is the step function.
Given *assumed* arguments n' and hn', a proof of
(sumToNProp n'), the *induction hypothesis* we
need to return a proof of (sumToNProp (n'+1)).

This is where proofs by induction generally pose
a challenge: defining the step function. Before
getting into Lean, let's just think about it.

Assume n' and a proof, ih = (sumToNProp n'), of
sumToN n' = n' * (n' + 1) / 2.

From that we need to construct a proof of the
output proposition, (sumToNProp (n'+1)). That in
turn is sumToN (n'+1) = (n'+1) * ((n'+1) + 1)/2.

The trick here is going to be to rewrite the left
side in a way that will let us use the induction
hypothesis to simplify what remains to be proved.

So turn attention to the definition of sumToN, and
in particular to the term, sumToN (n' + 1). What
it means is 0 + ... + n' + (n' + 1). KEY IDEA: We
rearrange this sum to (0 + ... + n') + (n' + 1)!
Now by the induction hypothesis we can replace
(0 + ... + n') with (n' * (n' + 1)) / 2!!! Now the
left side becomes (n' * (n' + 1)) / 2 + (n' + 1),
with right side still (n' + 1) * ((n' + 1) + 1) /2.

KEY IDEA: rewrite expressions so that you can then
use the induction hypothesis to simplify what needs
to be proved.

Are these two expressions equal? To show that they
are just requires some algebraic manipulations. A
major problem for many students is that they just
don't remember their algebra, or whatever other math
is needed, to prove formulas like this. Let's see
this one in detail.

We can rewrite the left side as follows:

- (n' * (n' + 1)) / 2 + (n' + 1)
- (n' * (n' + 1)) / 2 + 2 * (n' + 1) / 2)
- ((n' * (n' + 1)) + (2 * n' + 1)) / 2
- (n'^2 + n' + 2n' + 2) / 2
- (n'^2 + 3n' + 2) / 2
- (n' + 1)(n' + 2) / 2
- (n' + 1)((n' + 1) + 1) /2

That's it. We've provided a proof for n = 0,
and we've proved, right here, that, for any n',
if sumToN n' = n'*(n'+1)/2, then sumToN (n'+1)
= (n'+1)*((n'+1)+1)/2, and that is all we need
to apply the principle of induction for natural
number arguments and we're done!
@@@ -/

/- @@@
A key to this proof was the observation that we can
write (sumToProp n'+1) as (sumToProp n') + (n'+1).
That's critical because the induction hypothesis
THEN gives us a way to rewrite (sumToProp n') as
n' * (n' + 1) / 2. Once we do that, the rest of
the proof is just algebra. So to ease the task of
writing the proof, let's prove that we can always
rewrite sumToN (n'+1) as (sumTo n') + n'+1. The
proof is simply by the definition of sumToN. Go
look at its definition; you'll see.
@@@ -/

def pf (n : Nat) : sumToN (n.succ) = (sumToN n) + (n.succ) :=
-- true by the definition of sumToN
-- see the the second rule for computing this function
by simp [sumToN]

/- @@@
Now we see how to define the step function. Here
is a formal definition in Lean.
@@@ -/

def sumStep :
      ∀ (n' : Nat),
      (h : sumToNProp n') →
      sumToNProp (n'+1) :=
      -- assume n' is arbitrary
      -- and induction hpothesis, h: that n' has the property
(fun (n' : Nat) (h : sumToNProp n') =>
    -- in this context prove sumToNProp (n'+1): that n'+1 does too
  -- note: the rest of the proof is in tactic mode
  -- open Lean infoview (CTRL/CMD-SHIFT ENTER) and step through!
  (by
    -- unfold definition of sumToNProp in goal
    unfold sumToNProp

    -- use pf above to rewrite (sumToN n'.succ) in goal
    rw [pf]

    -- distribute multiplication by 2 in goal
    rw [Nat.left_distrib]

    -- rewrite (sumToN n') using induction hypothesis (!!!)
    rw [h]

    -- simplify the goal a little using basic algebra
    simp []

    -- use axioms of arithmetic with + and * to simplify both sides
    ring
    -- the result is an equality, which ring handles with rfl
    -- QED.
  )
)


/-
Here then is a final proof in Lean for what we
have already proved by hand / in English, by the
explicit application of the induction axiom for
Nat.
@@@ -/
def pfSumToNPropAll : sumToNPropAll :=
@Nat.rec      -- apply induction
  _           -- type of proof (inferred)
  sumZero     -- proof for base case, Nat.zero
  sumStep     -- proof buider, for case Nat.succ

-- That's it! pfSumToNPropAll will now give a proof for any n
-- Here's one for n = 13, for example
#check pfSumToNPropAll 13


/-
Here's some nicer syntax for the same proof by induction.
The proof is constructed entirely in tactic mode here.
The comments, though, should all make sense.

@@@ -/
example : sumToNPropAll :=
-- again in tactic mode
-- open infoView (CMD/CTRL-SHIFT-ENTER/RETURN)
-- then step through proof script one line at a time
(by
  -- by the definition of sumToNPropAll
  unfold sumToNPropAll
  -- we are to prove ∀ (n : ℕ), sumToNProp n
  -- start by assuming n is an arbitrary Nat
  intro n
  -- complete proof by induction
  induction n with
    -- case for n = 0
    | zero => exact rfl
    -- case n > 0
    -- if given any n and a proof/value for n
    -- constructs and returns a proof/value for n+1
    | succ n ih => exact (sumStep n ih)
)
