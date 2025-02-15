/- @@@
# Quantifiers: Existential Quantification (∃)

<!-- toc -->


We now turn to the second of the two quantifiers in
predicate logic: the existential operator, *∃.* It is
used to write propositions of the form, *∃ (x : T), P x*.
This proposition is read as asserting that *there is some
(at least one) value of type, T, that satisfies P*. As
an example, we repeat our definition of the *is_even*
predicate, and then write a proposition asserts that
there is (there exists) *some* even natural number.
@@@ -/

-- Predicate: defines property of *being even*
def isEven : Nat → Prop := λ n => (n % 2 = 0)
-- λ means the same thing as fun: a function that ...

-- Proposition: there exists an even number
#check ∃ (n : Nat), isEven n

/- @@@
## Introduction

In the *constructive* logic of Lean, a proof of
a proposition, *∃ (x : T), P x*, has two parts. It's
a kind of ordered pair. What's most interesting is that
type of value in the second element depends on the value
of th element in the first position.

The first elementis a specific value, *w : T* (a value,
w, of type T). What's new is the idea that the *type* of
the second element, *(P w)*, the proposition obtained by
applying P to w, *depends on w*. The return type, here,
depends on the value, *w*, of the *argument*. It must
be a proof of *P w*, which in turn is read as stating
that w has property P (e.g., of being even, equal to
zero, prime, odd, a perfect square, a beautiful number).

So there you have the *exists introduction* rule.
Apply Exists.intro to a witness (of the right type),
and a proof that particular witness *does* have that
property, as demonstrated by a formally checked proof
of it.

In type theory, proofs of existence are *dependent pairs*.

Here's a simple example showing that there exists an even
number, with *4* as a witness.
@@@ -/

example : exists (n : Nat), isEven n := Exists.intro 4 rfl

/- @@@
The witness is 4 and the proof (computed by rfl) is a
proof of 4 % 2 = 0, which is to say, of 0 = 0. Try *5*
instead of *4* to see what happens.
@@@ -/

/- @@@
Lean provides ⟨ _, _ ⟩ as a notation for Exists.intro.
@@@ -/

example : ∃ (n : Nat), isEven n := ⟨ 4, rfl ⟩

/- @@@
English language rendering: We are to prove that some
natural number is even. To do so we need to choose a
number (will will cleverly pick 4) and then also give
a proof that *4 is even*, which we formalizes as the
proposition resulting from the application of isEven
(a predicate taking a Nat) to 4.
@@@ -/

/- @@@
Another example: Suppose we have a proof that Iris is
a blue dog. Can we prove that there exists a blue dog?
@@@ -/

namespace bluedog
variable
  (Dog : Type)                 -- There are dogs
  (Iris : Dog)                 -- Iris is one
  (Blue : Dog → Prop)          -- The property of being blue
  (iris_is_blue : Blue Iris)   -- Proof that Iris is blue

-- A proof that there exists a blue dog
example : ∃ (d : Dog), Blue d := ⟨ Iris, iris_is_blue ⟩
end bluedog

/- @@@
## An Aside on Constructive Logic

The term *constructive* here means that to prove that
something with a particular property exists, you have
to actually have such an object (along with a proof).
Mathematicians generally do *not* require constructive
proofs. In other words, mathematicians are often happy
to show that something must exist even if they can't
construct an actual example.

We call proofs of this kind non-constructive. We saw
a similar issue arise with proofs of disjunctions. In
particular, we saw that a *constructive* proof of a
disjunction, *X ∨ ¬X,* requires either a proof of *X*
or a proof of *¬X*. Accepting the law of the excluded
middle as an axiom permits non-constructive reasoning
by accepting that *X ∨ ¬X* is true without the need
to construct a proof of either case.

What one gains by accepting non-constructive reasoning
is the ability to prove more theorems. For example, we
can prove all four of DeMorgan's laws if we accept the
law of the excluded middle, but only three of them if
not.

So what does a non-constructive proof of existence look
like? Here's a good example. Suppose you have an infinite
sequence of non-empty sets, *{ s₀, s₁, ...}. Does there
*exist* a set containing one element from each of the sets?

It might seem obvious that there is such a set; and in
many cases, such a set can be *constructed*. For example,
suppose we have an infinite sequence of sets of natural
numbers (e.g., { {1, 2}, {3, 4, 5}, ... }). The key fact
here is that every such set has a smallest value. We can
use this fact to define a *choice function* that, when
given any such set, returns its smallest value. We can
then use this choice function to define a set containing
one element from each of the sets, namely the smallest
one.

There is no such choice function for sets of real numbers,
however. Certainly not every such set has a smallest value:
just consider the set {1, 1/2, 1/4, 1/8, ...}. It does not
contain a smallest number, because no matter what non-zero
number you pick (say 1/8) you can always divide it by 2 to
get an even smaller one. Given such a set there's no choice
function that can reliably returns a value from each set.

As it turns out, whether you accept that there exists a
set of elements one from each of an infinity of sets, or
not, is your decision. If you want to operate assuming that
there is such a set, then you accept what mathematicians
call the *axiom of choice*. It's another axiom you can add
to the constructive logic of Lean without causing any kind
of contradictions to arise.

The axiom of choice is clearly non-constructive: it gives
you proofs of the existence of such sets for free. Most
working mathematicians today freely accept the axiom of
choice, and so they accept non-constructive reasoning.

Is there a downside to such non-constructive reasoning?
Constructive mathematicians argue yes, that it leads to
the ability to prove highly counter-intuitive results.
One of these is called the *Banach-Tarski* paradox: a
proof (using the axiom of choice) that there is a way
cut up and reassemble a sphere that doubles its volume!
(Wikipedia article here.)[https://en.wikipedia.org/wiki/Banach%E2%80%93Tarski_paradox]
@@@ -/

/- @@@
As with excluded middle, you can easily add the axiom
of choice to your Lean environment to enable classical
(non-constructive) reasoning in Lean. We will not look
further into this possibility in this class.
@@@ -/

/- @@@
## Elimination Rule for ∃

Now suppose you have a proof of a proposition, *∃ (x : T),
P x*. That is, suppose you have *pf : ∃ (x : T), P x.* How
can you *use* such a proof?

Here's the key idea: if you know that *∃ (x : T), P x*,
then you can deduce two facts: (1) there is some object,
call it *(w : T),* for which, (2) there is a proof, *pw*,
that *w* satisfies *P* (a proof of *P w*). The elimination
rule gives us these objects to work with.

Recall that the introduction rule takes a specific value,
*w*, and proof, *pf : P w,* that that value has property
*P*. Elimination destructures such a proof. What is gives
you back, however, is not the *specific* witness used to
create the proof, but rather than arbitrary value, *w : T*,
along with a proof of *P w*. For this reason, you will see
that proofs of existence are called *information hiding*
objects. A specific witness is no longer availabe from a
proof of existence.
@@@ -/

/- @@@
### Examples

Here's an example. We want to show that if we have a proof,
*pf*, that there's a natural number, *n*, that satsifies
*True* and *isEven*, then there's a natural number, *f*,
that satisfies just *isEven*.
@@@ -/

def ex1 :
  -- Prove:
  (∃ (n : Nat), True ∧ isEven n) → (∃ (f : Nat), isEven f) :=
  -- Proof: by "arrow/function introduction" (from premise, prove conclusion)
  -- assume some proof h, of (∃ (n : Nat), True ∧ isEven n)) and thern ...
  fun (h: (∃ (n : Nat), True ∧ isEven n)) =>
    -- show (∃ (f : Nat), isEven f).
    -- The proof is by exists elimination ...
    -- ... essential here because it gives us a witness to use in proving the conclusion
    Exists.elim
      -- applied to h, a proof (∃ (n : Nat), True ∧ isEven n) ...
      h
      -- a proof that
      (
        --  from any natural number, a, and ...
        fun (a : Nat) =>
        (
          -- a proof that a satisfies (True ∧ (Even n))
          fun tea =>
            -- there is a proof of (∃ (f : Nat), isEven f).
            -- the proof is by the rule of exists introduction ...
            Exists.intro
              -- using the "abstracted" witness obtained by elimination of the premise ...
              a
              -- and a proof of (isEven a), obtained by right and elimination applied to
              -- obtained from the proof of (True ∧ isEven a) by the rule of right and elimination
              (tea.right)
        )
      )


/- @@@
To this end. delete everything from fun to the end and put
(_) in its place. Next, use Lean to display, and understand,
what type of value is needded. Provide a complete term of that
type if you can, but in any case apply the right inference
rule to as many of its arguments as you have, arranging the
actual arguments vertically indented and with (_) for each
of the arguments to be filled in subsequently. And now just
elaborate what goes in each of those "holes", until you get
to the bottom of the proof object (here, at *tea.right*). You
can't just read the text, you have to watch and experience
the emergence of the proof, largely at this point fron the
mere syntactic forms of the propositions being proved all
along the way.
@@@ -/

/- @@@
The preceding expression of the proof explicitly applies
inference axioms without Lean-provided concrete notations.
The following expression of the proof uses concrete notations.

Here's what that looks like. Lean packs all of the above into
the often more compact and humanly interpretable "by case analysis
syntax using pattern matching" notation. Here's that very same
proof presented in this more conventional notation. in
Lean. This notation, by the way, is largely adopted from Haskell,
a historically and practically important programming language. It
ushered in numerous fundamental constructs now deeply embedded not
only into Lean but a broad swatch of functional languages. Others
include, for example, OCaml, SML, etc. The Coq proof assistant, a
most interesting, still important, antecedent of Lean, is written
in OCaml, so with Coq, it's all the same ideas we've been learning
but in OCaml-like syntax rather than Haskell-like syntax. Cool, eh!
A great mind exercise is to read through the completely desugared,
pure functional proof construction, and see where each element in
that definition is reflected in the one using Haskelly notation,
here.
@@@ -/

def ex1' :
  (∃ (n : Nat), True ∧ isEven n) →
  (∃ (f : Nat), isEven f)
| ⟨ w, pf_w ⟩  => Exists.intro w pf_w.right


/- @@@
Note: In commonplace mathematical lingo, a theorem is often
thought of as a "true proposition:" for which a proof has
been given. There's also a purely social convention around
using the word, theorem. A theorem is an "important" truth,
often the "main result" of a mathematical research project.
To produce such a proof it's often important to prove one or
more "smaller" propositions along the way. The word used for
these is usually "lemma." Finally, facts that follow from the
truth of a theorem are usually called "corollaries."

Lean4 does support use of the word, theorem, instead of def,
when defining a proof of a proposition. It is just a nicety
with no real additional importance. No need to be perplexed
by it. Just read it as "def."
@@@ -/


--------
/- @@@
way to apply elimination is by pattern matching,
as in the following example. It shows that if there exists a
number that's true and even, then there's a natural number
that's even. Note that what matching gives you is not the
specific value used to form the proof, but an *arbitrary*
value, *w* and a proof *pf : P w.* That is what you have
to work with after applying the elimination rule.
@@@ -/

/- @@@
To show this we destructure *pf* as *⟨ w, pf_w ⟩*. This
gives us a witness, *w : Nat* (whose value we do not know),
along with a proof, *pf_w*, that *w* (whatever value it is)
satifies both *True* and *is_even.* Surely then *w* satisfies
*is_even* by itself. That's the insight.

We can thus form the desired proof by applying Exists.intro
to *w* and a proof that *w* satisfies *is_even.* Here *w*
is the witness (value unknown) obtained by destructuring the
assumed proof of the premise. We know it's and so will be able
to use it as a witness in a proof that there is an even number.
Now *pf_w* is then an assumed proof that *w* satisfies both
*True* and *is_even*. From this proof we can derive a proof
that *w* satisfies *is_even* (by and elimination right). To
prove there exists an even number, then, we just apply
Exists.intro to *w* and to *pf_w.right*. (You can use *.2*
instead of *.right* in this expression).

In English we might say this. Prove that if there's a number
that is True and even then there's a number that's even.

Proof: Assume there's a number that is True and even. We
can then deduce that there is number, *w*, for which there
is a proof, *pf* that *w* is *True* and *w* is *even*.
From that proof, *pf,* by *and elimination right,* we can
deduce there's a proof, *pf_w_even*, that *w* is even.
So we now have a witness, *w*, and a proof that *w* is
even, so we can form a proof that there exists a number
that's even: ⟨ w, pf_w_even ⟩.
@@@ -/




--------

theorem ex1'' :
  (∃ (n : Nat), True ∧ isEven n) →
  (∃ (f : Nat), isEven f)
| ⟨ w, pf_w ⟩  => Exists.intro w pf_w.right

/- @@@
## Worked Exercise

Formalize and prove the proposition that if there's
someone everyone loves, then everyone loves someone.

An informal, English language proof is a good way to
start.

Proof. Assume there exists someone, let's call them *Beau*,
whom every person, *p*, loves. What we need to show is that
everyone loves someone. To prove this generaliation, we'll
assume that *p* is an *arbitrary* person and will show that
there is someone *p* loves. But everyone loves *beau* so,
by universal specialization, *p* loves Beau. Because *p* is
arbitrary, this shows (by *forall introduction*) that every
person loves someone (namely *beau*).
@@@ -/

namespace cs2120f23
variable
  (Person : Type)
  (Loves : Person → Person → Prop)

example :
  (∃ (beau : Person), ∀ (p : Person), Loves p beau) →
  (∀ (p : Person), ∃ (q : Person), Loves p q)

-- call the person everyone loves beau
-- call the proof everyone loves beau everyone_loves_beau
| ⟨ beau, everyone_loves_beau ⟩  =>
-- prove everyone loves someone by ∀ introduction
-- assume you're given an arbitrary person, p
    fun (p : Person) =>
-- then show that there exists someone p loves
-- with beau as a witness
-- and a proof p loves beau (by universal specialization)
    ⟨beau, (everyone_loves_beau p)⟩
end cs2120f23

/- @@@
Here's the same logical story presented in a
more abstract form, using *T* instead of *Person*
and *R : T → T → Prop* to represent the binary
relation (previously *Loves*) on objects of type
*T*.
@@@ -/

variable
  (T : Type)
  (R : T → T → Prop)

-- Here
example : (∃ (p : T), (∀ (t : T), R t p)) →
          (∀ (p : T), (∃ (t : T), R p t))
| ⟨ w, pf_w ⟩ => (fun (p : T) => ⟨ w, pf_w p ⟩)

/- @@@
In mathematical English: Given a binary relation,
*R*, on objects of type *T*, if there's some *p*
such that forall *t*, *R t p* (every *t* is related
to *p* by *R*), then for every *p* there is some *t*
such that *R p t* (every *p* is related to some *t*).
In particular, every *p* is related to *w*, the person
*everyone* loves. So everyone loves someone.
@@@ -/

/- @@@
## Homework

Forthcoming.
@@@ -/
