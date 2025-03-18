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

```lean
-- Predicate: defines property of *being even*
def isEven : Nat → Prop := λ n => (n % 2 = 0)
-- λ means the same thing as fun: a function that ...

-- Proposition: there exists an even number
#check ∃ (n : Nat), isEven n
```



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
-/

#check Exists.intro

```lean
```lean
Exists.intro.{u}
  {α : Sort u}    -- Given any type α
  {p : α → Prop}  -- Given any predicate, p, on α
  (w : α)         -- Provide a witness, a, of type α
  (h : p w) :     -- And a proof of the proposition (p a)
Exists p
```
```

/-
In type theory, proofs of existence are *dependent pairs*,
of the form, *⟨a : α, h : p a⟩. Note carefully that the type
of the second element, namely a proof of *(p a)*, depends on
the value of the first element, *a*.

### Example: There is some even number

Here's a simple example showing that there exists an even
number, with *4* as a witness.

```lean
example : exists (n : Nat), isEven n := Exists.intro 4 rfl
```

The witness is 4 and the proof (computed by rfl) is a
proof of 4 % 2 = 0, which is to say, of 0 = 0. Try *5*
instead of *4* to see what happens.

Lean provides ⟨ _, _ ⟩ as a notation for Exists.intro.

```lean
example : ∃ (n : Nat), isEven n := ⟨ 4, rfl ⟩
```

We will study the equality relation shortly. For now,
know that *rfl* produces a proof that a value equals
itself, and that's exactly what we need to construct
the second element of this pair.

English language rendering: We are to prove that some
natural number is even. To do so we need to choose a
number (will will cleverly pick 4) and then also give
a proof that *4 is even*, which we formalizes as the
proposition resulting from the application of isEven
(a predicate taking a Nat) to 4.

### Example: There is some Blue Dog

Another example: Suppose we have a proof that Iris is
a blue dog. Can we prove that there exists a blue dog?

```lean
namespace bluedog

variable
  (Dog : Type)                 -- There are dogs
  (Iris : Dog)                 -- Iris is one
  (Blue : Dog → Prop)          -- The property of being blue
  (iris_is_blue : Blue Iris)   -- Proof that Iris is blue

-- A proof that there exists a blue dog
example : ∃ (d : Dog), Blue d := ⟨ Iris, iris_is_blue ⟩

end bluedog
```



## Elimination

Now suppose you have a proof of a proposition, *∃ (x : α),
P x*. That is, suppose you have *pf : ∃ (x : α), P x.* How
can you *use* such a proof to derive a proof of some other
proposition, let's call it *b*. The goal is to understand
when *∃ x, P x → b*.

Here's the key idea: if you know that *∃ (x : T), P x*,
then you can deduce two facts: (1) there is some object,
call it *(w : T),* for which, (2) there is a proof, *pw*,
that *w* satisfies *P* (a proof of *P w*); and then, if
in addition to having such a witness, we know that if all
objects of type α satisfy *P* implies *b*, then *b* must
be true, by application of *∀ elimination* to *w*. The
elimination rule gives us these objects to work with.

```lean
#check Exists.elim
```

```lean
Exists.elim.{u}
  {α : Sort u}                  -- Given any type, α
  {p : α → Prop}                -- Given any predicate on α
  {b : Prop}                    -- Given a proposition to prove
  (h₁ : ∃ x, p x)               -- If there's an x satisfying p
  (h₂ : ∀ (a : α), p a → b) :   -- If every a satisfies p implies b
b                               -- then b
```

### Example

Here's an example. We want to show that if we have a proof,
*pf*, that there's a natural number, *n*, that satsifies
*True* and *isEven*, then there's a natural number, *f*,
that satisfies just *isEven*.

```lean
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

def ex1' :
  (∃ (n : Nat), True ∧ isEven n) →
  (∃ (f : Nat), isEven f)
| ⟨ w, pf_w ⟩  => Exists.intro w pf_w.right


-- Using better notation
theorem ex1'' :
  (∃ (n : Nat), True ∧ isEven n) →
  (∃ (f : Nat), isEven f)
| ⟨ w, pf_w ⟩  => Exists.intro w pf_w.right
```

### If There's Someone Everyone Loves then Everyone Loves Someone

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

```lean
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
```

Here's the same logical story presented in a
more abstract form, using *T* instead of *Person*
and *R : T → T → Prop* to represent the binary
relation (previously *Loves*) on objects of type
*T*.

```lean
variable
  (T : Type)
  (R : T → T → Prop)

-- Here
example : (∃ (p : T), (∀ (t : T), R t p)) →
          (∀ (p : T), (∃ (t : T), R p t))
| ⟨ w, pf_w ⟩ => (fun (p : T) => ⟨ w, pf_w p ⟩)
```

In mathematical English: Given a binary relation,
*R*, on objects of type *T*, if there's some *p*
such that forall *t*, *R t p* (every *t* is related
to *p* by *R*), then for every *p* there is some *t*
such that *R p t* (every *p* is related to some *t*).
In particular, every *p* is related to *w*, the person
*everyone* loves. So everyone loves someone.

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

As with excluded middle, you can easily add the axiom
of choice to your Lean environment to enable classical
(non-constructive) reasoning in Lean. We will not look
further into this possibility in this class.
