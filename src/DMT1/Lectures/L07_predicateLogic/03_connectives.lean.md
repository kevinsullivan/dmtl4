# The Logical Connectives in Type Theory

<!-- toc -->


If you come to understand the following ideas, and can use them, then
you've understood how to represent complex logical expressions in type
theory.

- propositions in type theory are always represented as types
- proofs of a proposition, if there are any, are represented as values of such types
- the ∧, ∨, ↔ (and ∃) connectives as represented as parameterized/polymorphic data type builders
- the introduction rules for ∧, ∨, ↔ (and ∃) are represented as constructors of such types
- → (and ∀) propositions are represented as function types
- proofs of → (and ∀) propositions are represented as implementations of such funciton types
- the elimination rules for ∧, ∨, ↔ (and ∃) are functions that destructure proofs to make new proofs
- the elimination rule for → (and ∀) is *function application*

We've already seen all of this in our case study of ∧ over the last two classes.
(1) The ∧ connective is represented by the polymorphic type, And : Prop → Prop → Prop.
(2) If P and Q are propositions, and p and q are proofs, Then (And.intro p q) is a proof of P ∧ Q
(3) Suppose h is a proof (And.intro p q) : P ∧ Q, then
    - And.left h (notation h.left, h.1) is p, a proof of P, proving P ∧ Q → P
    - And.right h (notation h.right, h.2) is q, a proof of Q, providing P ∧ Q → Q
(4) With that we can prove such facts as P ∧ Q → Q ∧ P
    - Define a function with argument (h : P ∧ Q); destructure h to get p, q; then (And.intro q p)

So there.

- The And connective is represented by the polymorphic And type builder.
- The introduction rule for And, (P → Q → P ∧ Q), is represented by its intro constructor.
- The elimination rules, (P ∧ Q → P), (P ∧ Q → Q) are represented by the left/right getter functions.

This lecture now takes you through the full set of logical connectives from propositional
logic, showing you how each logical connective is represented as a polymorphic data or function
type, its introduction rules, and its elimination rules.

So as to be able to illustrate these ideas, let's suppose/assume (using Lean's "axiom"
keyword) that we have (1) three arbitrary propositions, P, Q, and R, along with a propostion,
F, defined explicitly as having no proofs; and (2) (p : P), (q : Q), and (r : R) are proofs
of P, Q, and R, respectively.

```lean
-- Propositions and proofs
axiom P : Prop              -- assume P is some proposition
axiom Q : Prop              -- assume Q is some proposition
axiom R : Prop              -- assume R is some proposition
inductive F : Prop where    -- define F as a proposition with no proofs

axiom p : P                 -- assume p is proof of P
axiom q : Q                 -- assume q is a proof of Q
axiom r : R                 -- assume r is a proof of R
```


## And

### ∧ Is Represented as a Polymorphic Proposition (Type) Builder

Here are the axioms for ∧ from our work on PL:

- and_intro :=      P ⇒ Q ⇒ P ∧ Q
- and_elim_left :=  P ∧ Q ⇒ P
- and_elim_right := P ∧ Q ⇒ Q

The mapping of these axioms into Lean is as follows:

- The ∧ connective maps to a polymorphic type, And α β, where α and β are propositions (as types)
- the intro rule maps to the intro constructor of this type
- the elimination rules map to getter/projection functions

We'll now take each of these aspects in turn.


#### The Syntactic ∧ Connective is Represented as a Polymorphic Type Builder

The ∧ connective is represented in the type theory of Lean
as a polmorphic type builder: And, with two two propositions
(types) as arguments. Applying And to two propositions, P, Q,
thus yields another proposition, namely P ∧ Q. The type of And
is thus Prop → Prop → Prop, making it a "binary operation" on
propositions, just as in propositional logic. Lean defines ∧
as a concrete notation for the polymorphic type builder, And.
```lean
#check (@And)     -- Prop → Prop → Prop
#check (And P Q)  -- a proposition (not a proof)
```

### The "Intro" Axiom is Represented as its Single Constructor

And now for the inference rules. The constructor, And.intro, has
the type, ∀ {a b : Prop}, a → b → a ∧ b. Don't be confused by the
use of "a" and "b" instead of P and Q here. These are just arbitrary
names. You can pronounce this type in English as follows: If we are
given any two propositions, a and b (represented as types in Prop),
and proofs of a and b, (p : a) and (q : b), the (And.intro p q) is
defined to be a value of type (And a b), which is to say that it
is accepted a proof of a ∧ b. Lean defines ⟨p, q⟩ as a shorthand
for (And.intro p q), emphasizing that a proof of a conjunciton is
in the form of a *pair* of proofs, one of a and one of b.

```lean
#check (@And.intro)
#check (And.intro p q)
```


### The "Elimination" Rules are Represented as its Getter Functions

When you use "structure" to define a single-constructor type in Lean,
Lean defines getter functions for you with the names of the fields (in
this case, left and right, respectively) as getter functions. Given a
proof, h = ⟨p, q⟩, (And.left h) returns p and (And.right h⟩ returns q.

```lean
#check (@And.left)            -- ∀ {a b : Prop}, a ∧ b → a
#check (@And.right)           -- ∀ {a b : Prop}, a ∧ b → b
#check (And.intro p q).left   -- ⟨p, q⟩.left : P
#check (And.intro p q).right  -- ⟨p, q⟩.right : Q
```


## Or

We've seen that if α and β are types in Prop, then And α β is also a
type in Prop. It's single constructor taking two values, (a : α) and
(b : β), makes it an example of what we can call a *product* type. It
has one constructor taking both (a : α) *and* (b : β) as arguments.

By contrast, *Or α β* is an example of what we can call a *sum* type,
or *variant* type. It has two constructors, inl (a : α) and inr (b : β).
This means that an arbitrary value of this type carries *either* a proof
(a : α) *or* a proof (b : β).

Here are the axioms for Or from our study of propositional logic.

- or_intro_left :=    P ⇒ P ∨ Q
- or_intro_right :=   Q ⇒ P ∨ Q
- or_elim :=          Q ∨ R ⇒ (Q ⇒ P) ⇒ (R ⇒ P) ⇒ P

And here's how Lean defines Or

inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b


### The Syntactic Or Connective is Represented as a Polymorphic Type Builder

Exactly the same narrative as for And applies to the Or connective.
First, it's represented as a polymorphic proposition/type builder.
Second, the introduction rules are represented by its constructors.
Finally, the elimination rule is represented by a function. Such a
function works by *case analysis*. Given a proof (h : Or α β), the
elimination rule uses pattern matching to determine whether h is of
the form, Or.inl a, *or* of the form, Or.inr b. It then derive a proof
of


```lean
-- The type of the Or proposition builder
#check (Or)
#check (Or P Q)
```

### The "Intro" Axioms are Represented as Constructor

```lean
#check (@Or.inl)
#check (@Or.inr)
#check (Or.inl p : P ∨ Q)
#check (Or.inr q : P ∨ Q)
```

### The Or Elimination Rule

```lean
#check (@Or.elim)   -- ∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
```

We can pronounce this inference rule in either truth-or proof-theoretical
forms. Here's the truth-theoretical reading. If a, b, and c are propositions,
then if at least one of a and b is true, then if it's true that if a is true
so is c, then if it's also true that if b is true so is c, then appling the
Or.elim inference rule shows that c must be true.

Here's a proof-theoretical reading, which is better in type theory. If a, b,
and c are propositions, then if *we have a proof* of a ∨ b, and then if we
have a function that converts any proof of a into a proof of c, and then if
we also have a function that converts any proof of b into a proof of c, then
an application of Or.elim to these three proofs reduces to (returns) a proof
of c.
```lean
#check (@Or.elim)   -- ∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
```

Note: The curly braces around { a b c : Prop }, rather than parentheses,
tells Lean to figure out the values of these type arguments from the remaining
arguments, so that you as the "programmer" don't have to supply these three
type arguments when applying the Or.elim rule. Note also that constructors of
polymorphic types are also polymorphic, taking type arguments *implicitly*.


## Equivalence

The ↔ connective is also defined as an inductive type in Lean. The basic
reasoning is that if you have a proof of P → Q, and you also have a proof
of Q → P, then you can deduce P ↔ Q. And if you have a proof of P ↔ Q, then
you can deduce (obtain proofs of) respectively, P → Q and Q → P.

As with ∧, a proof of P ↔ Q has the form of a pair of proofs, one of
P → Q and one of Q → P. Thus ↔ is defined almost identically to ∧, except
now the two proof arguments to Iff.intro have to be proofs of P → Q and
Q → P, in particular. As proofs of implications are functions, a proof of
P ↔ Q in type theory has the form of a pair of functions!

structure Iff (a b : Prop) : Prop where
  intro ::
  mp : a → b
  mpr : b → a

The names of the arguments are abbreviations for modus ponens and
modus ponens reverse. Modus ponens (latin) was Aristotle's rule that
if (P → Q) and P then Q. What mp and mpr are express is the same idea
but for ↔. If (P ↔ Q) and P then Q, and if (P ↔ Q) and Q then P.

### The Polymorphic ↔ Proposition/Type Builder

The Iff proposition/type (builder), with two proposition arguments
```lean
#check (@Iff)
#check (Iff P Q)
```

### The ↔ Intro Inference Rule
```lean
#check (@Iff.intro)
```

### The ↔ Elim Rules

The elimination rules are just the two "projection" (getter) functions.
Their names are abbreviations for "modus ponens (for Iff)" and "modus
ponens reversed (for Iff)." The name "modus ponens" comes from Aristotle!
```lean
#check (@Iff.mp)    -- if we know a ↔ b and we know a then we know b
#check (@Iff.mpr)   -- if we know a ↔ b and we know b then we know a
```



## Implication

In type theory, we don't give a proof of an implication as a data
structure (that is, as a value of an inductive type); rather a proof
of a logical implication, P → Q in type theory has the form of a
function, f : P → Q.

### Introduction Rule

As stated, a proof of P → Q is given as a function of type P → Q. In
English, we'd say, "If whenever we have a proof of P we can derive a
proof of Q then we can conclude that P → Q." That's all there is to it.

Another way to say this is that if we have a function that, when applied
to any proof of P constructs and returns a proof of Q, then if P is true,
as shown by having a proof, p, of it, then Q must be true, as f applied
to p reduces to a proof of Q, showing that it must also be true.

### Elimination Rule

The elimination rule is what Aristotle called modus ponens. If we
have a value/proof (pf : P → Q, where pf is now a function that takes
any P value/proof and returns a Q value/proof), and if we also have a
of proof P, then a proof of Q can be constructed, showing Q to be true.
That proves P → Q. Note that it is not always possible to define a
function that *can* construct a proof of Q from a proof of P. Where
it's not possible, we'd judge P → Q to be false.

Here's another way to think of it. P → Q is a type. Values of such a
type are functions that turn proofs of P into proofs of Q. If there
is no such function the from a proof of P it's simply not possible to
derive a proof of Q. In other words, P → Q is true if there's a value
of this type (a function); but if P → Q is an uninhabited type, then
we'd judge that P → Q is false.

Now recall from above that we've assumed we have propositions P and Q.
Let's in addition now assume that we have a proof, (pimpq : P → Q). It
is a function. The elimination rule is *function application*. Given
this proof, and given that we already assumed a proof of P, (p : P),
all we have to do is apply pimpq to p to get a proof of Q.

```lean
#check P → Q          -- a proposition
axiom pimpq : P → Q   -- suppose we have a proof of it, pimpq
#check (pimpq p)      -- *Applying* it to pimpq yields a proof of Q
```


### Summary

To construct a proof of an implication, P → Q, in type theory, define a
function of type P → Q. If there is no function/proof of (type) P → Q,
then P → Q is false. To *use* a proof of P → Q, apply it to a proof of P
to obtain a proof of Q.


### True

The "always true" proposition (which we wrote as top, ⊤, in PL, is realized
in type theory as the proposition (type), True : Prop. The True proposition
has one proof/constructor. It is called intro and takes no arguments at all.
So there's always a proof of True, namely True.intro, making it always True.
Here's the definition of True from Lean's core libraries.

inductive True : Prop where
  | intro : True                -- True.intro is a proof of True

```lean
#check True                     -- a proposition
```

### Introduction Rule

True.intro is the name of the single proof of True in Lean, If ever
you need a proof of true, just write True.intro. It is rare, almost
never, that you actually need to have a proof of true. Nothing can
be deduced from it, so it's really of little to no use in practice.

```lean
#check True.intro               -- the always available proof of True

/-
### Elimination Rule

Because nothing else can be derived from a proof of True, there is
no useful elimination rule for this proposition.
```



```lean
## False

In Type theory (in Lean), False is the always false proposition, akin
to ⊥ in propositional logic. False is false in type theory because it
is defined as a proposition with no proofs at all (no constructors). In
Lean, here's its definition.

inductive False : Prop

That's it!
```

#check False

```lean
### Introduction Rule

As False has no proof constructors, there are no proofs of it at all.
This is the representation in type theory of the fact that there is no
introduction rule for False. That is true in both propositional logic
and in the much richer logic of type theory.
```

```lean
### Elimination Rule

Please take a moment to revisit our axioms for propositional logic.
The false_elim rule can be read as asserting that if false is true
then anything is true (⊥ → P). Once again, this already familiar rule
maps directly into type theory, but now as a rule that says that if
P is any type (whether a propositional or an ordinary data type), then
False → P. From False *anything* follows. In Latin, ex falso quodlibet.
```

#check (@False.elim)      -- {C : Sort u_1} → False → C

```lean
Let's unpack the type of False.elim. First, it's a chained implication,
so we start with "If." If we're given any type, C (whether a proposition
or any other type, which is what Sort u_1 means here) then if we're also
given a proof of False, then a value of type C (a proof if C : Prop) can
be returned. That's ok because there is no proof of False.

Note: The argument, C, is declared within curly braces, {_}. What this
notation tells Lean is that when applying False.elim, one should not
have to give that first argument explicitly (a type), because Lean can
figure out what value it must have from the surrounding context, namely
from the appearance of C as the return type.

As an example, here's a formal proof that False implies 0 = 1. That
is, if False is true (with some proof, f) then a proof value for the
proposition (type) 0 = 1, can be constructed and returned. This is a
true statement, but only because the premise can't be true, so there
will never be any need to construct a proof of 0 = 1.
```

example : False → 0 = 1
| f => False.elim f -- No need to supply 0=1 an explicit type argument

-- One can tell Lean to disable this kind of type inference using @

example : False → 0 = 1
| f => @False.elim (0 = 1) f  -- @: the type argment must now be given explicitly

```lean
So why does the false elimination rule make sense? Let's see. To prove
False → 0 = 1, we have to show that if a function *assumes* it gets a
proof of False as an argument, then all it has to do is convert every
value/proof of that into a proof of 0 = 1. But there are no proofs of
false, so no conversion procedures need to be defined at all! That's it.

So now getting down to Lean-specific details, if f is an assumed proof
of False, the term "nomatch f" tells Lean that there are no cases to
consider, so there is no need to construct an actual value of the return
type. It's a way of saying that this case can never occur, so just don't
worry about it!

Here are two examples. In the first case, the return type, Nat,
is in Type. In the second case, it's in Prop, so the definition
of the function serves as a proof that (False → 0 = 1) is true.
```

def false_imp_nat : False → Nat
| f => nomatch f

def false_imp_bad : False → 0 = 1
| f => nomatch f

```lean
DMT1 Class of 10/31 ended here
```

```lean
### Examples: Implications Between True and False

Let's see how implications between True and False in
type theory exactly mirror those between ⊤ and ⊥ in
propositional logic.
```

-- True → True is valid
example : True → True
| t => t                  --given a proof of true, we can have a proof of true

-- An implication with a true conclusion is always true
-- Just ignore the argument and return a proof of the conclusion
example : True → True
| _ => True.intro


-- True → False is *not* valid
example : True → False
| t => _                  -- there is no proof of False

-- False → True is valid
example : False → True
| _ => True.intro         -- Here we just return a proof of True

-- Another proof of False → True is valid
example : False → True
| f => nomatch f          -- Or we can do a case analysis on f
                          -- nomatch just applies False.elim

-- False → False is valid
example : False → False
| f => f    -- Given an assumed proof of false, just return it

-- Or use False.elim to the same effect
example : False → False
| f => False.elim f    -- Given an assumed proof of false, just return it

-- Or show that there are simply no cases to consider
example : False → False
| f => nomatch f

```lean
As a final note, you can consider any uninhabited type to be false.
Recall that we defined F to be an proposition with no proofs. We
can show that if there's a proof of it (which there isn't!) then we
can have a proof of False.
```

example : F → False
| f => nomatch f

```lean
A function argument, of an uninhabited type (such as F) states
that the function can *assume* it's applied to a value of that
type; but there are none, and nomatch f is the way to tell Lean
to verify that and return without actually providing any value
at all. That, in turn is ok because the function can never really
be called, because there are no values of the type required to
apply the function. It can never be called.

As a final note, False is the standard empty type in Prop. In
Type, in Lean, the empty "computational as opposed to logical"
type is called Empty. The same reasoning applies here. We can
define a function from Empty to anything because there are no
values to apply it to, and so no cases to consider to define
the function.
```

example : Empty → False
| e => nomatch e


```lean
## Not

In the preceding section we proved that F → False, where
F is a proposition without any proofs (an uninhabited type).
The proof is by case analysis on all possible values of F,
of which there are none.
```

example : F → False
| f => nomatch f


```lean
If F had at least one value, we'd have to judge it to be true,
and in this case we'd be trying to prove that true implies false,
which is wrong. Fortunately, if F is true with some proof f, then
we'd never be able to define a function from F to False because
when applied to that value, f, the function would have to return
an actual proof of False, but that's impossible. For example, we
cannot prove P → False because there is at least one proof of P.
If we try, Lean will say we've failed to define a return value
for that (or those) cases.
```

example : P → False
| pf => nomatch pf

```lean
So, what we've now seen is that we can define a function from
a proposition, P, to False, if and only iff P has no proofs, in
which case we can judge that P is false, *in which case we can
now say that ¬P must be true: ¬P must have a proof!

So now we have a basis for defining ¬P? In type theory this
proposition is simply defined to mean the proposition, P → False!
So to prove ¬P, just prove P → False; and to use a proof of ¬P,
apply it to a proof of P to derive a proof of False.  Read the
documentation string that pops up when you hover over Not. It
should echo what we've just said here. Here's the definition of
Not in Lean's library (with ¬ as a concrete notation): it takes
a proposition a and returns the proposition a → False.

def Not (a : Prop) : Prop := a → False
```

#check @Not
#print Not

```lean
As a small example, we'd expect ¬False to be true. That is,
we expect there to be a proof of False → False. That is, we
expect there to be a function of type False → False. And we
already proved that there is such a function. We gave three
equivalent presentations of this function in the last section.

Similarly, we'd expect ¬F to be true, which is to say that
we expect that we *can* define a function of type F → False,
which we can read as saying that *if* there's a proof of F,
then there's a proof of False; and no proof of False exists,
so no proof of F can exist, and in this case we can conclude
that ¬F must be true.
```

example : ¬F    -- trick: you *must* treat ¬F as F → False
| f => nomatch f

/-
Now recall our PL axioms for negation (¬). In PL the
introduction rule states (P → ⊥) → ¬P. Yay, that's just
what we're seeing here: If P being true implies false is
true, then P cannot be true and in this case ¬P must be.
The definition of Not (¬) in Lean is directly analogous:
if (P → False) is true, then you can conclude ¬P is true.

```lean
/-
### Introduction Rule for Not (¬)
Given all that, we can see that to prove ¬P one simply proves
P → False. The latter proposition is an implication. And as you
already know, to prove implication in type theory you define a
function. The preceding proof of ¬F serves as an example.
```

```lean
### Elimination Rule for ¬

Now we've seen that a proof of ¬F in type theory is a function
of type F → False. So if you *have* a proof of ¬F, you have a
proof of F → False. This proof/function converts any proof of
F into a proof of False, then you can apply False.elim to be done.
The elimination rule for a proof, nf, of ¬F is to *apply* nf, as
a function, to a proof of F.
```

def nf : ¬F
| f => nomatch f

def badfun : F → False
| f => False.elim (nf f)  -- nf applied to f is a proof of False

def badfun2 : F → False
| f => nomatch f          -- it's easier to write using nomatch

-- Yay!

```lean
## Examples

### And (∧)
```

```lean
#### Introduction
```

```lean
Here we apply And.intro to construct proofs of P ∧ Q.
In each case it's by applying the proof/value constructor,
And.intro to arguments, p and q, of types P and Q, respectively.
The first example binds a name to the resulting proof so we can
use it later. The second example checks the proof but doesn't
give it a name. The third example presents concrete notation,
defined in Lean's libraries, for And.intro _ _
```
def pandq : P ∧ Q := And.intro p q
example   : P ∧ Q := And.intro p q
example   : P ∧ Q := ⟨ p, q ⟩

```lean
#### Elimination

From a proof, pandq, of P ∧ Q, we can derive proofs of P and
of Q, respectively. We do this by destructuring a given proof,
such as pandq. There's only one constructor, but destructuring
let's us get at the two smaller proofs from which any such term
must have been constructed. It's especially easy to apply the
elimination rules because (1) there's one constructor, And.intro,
(2) the type is defined using the "structure" keywords, and (3)
as a result of that, we can use the names of the fields, given
in the definition of And, to retrieve that arguments that were
given to And.intro when the value was constructed.
```
example : P := pandq.left
example : Q := pandq.right
example : P := pandq.1
example : Q := pandq.2

```lean
A little theorem
```

example : P ∧ Q → Q ∧ P
| And.intro p q => And.intro q p



```lean
### Or (∨)

#### Introduction

A proof of P ∨ Q can be constructed from a proof (p : P) or
from a proof (q : Q), for which we have the two constructors,
Or.inl and Or.inr.
```

def porqFromP : P ∨ Q := Or.inl p
def porqFromQ : P ∨ Q := Or.inr q

```lean
Elimination
```

#check (@Or.elim)

/-
The check shows the type of Or.elim.  It's a function of this type:
∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c. It says that if a,
b, and c are any propositions, then if you have a proof, (h : a ∨ b),
then if we also have proofs, (ac : a → c), and (bc : b → c), then in
either case of h (one carryiny a proof of a, and the other a proof of
b) we can construct a proof of c, by applying either ac or bc to the
proof of a in the first case and b in the second case. This will show
that if you have *any* proof of a ∨ b along with proofs of ac and bc,
then you can derive a proof of c.

To see this rule in actions, let's just assume, without being specific,
that we do have have proofs of ac : a → c and bc : b → c. They will be
in the form of functions, as we've seen several times now. Because we've
already defined R to be an empty type, we'll introduce one more type, S,
to illustrate these ideas.

```lean
axiom S : Prop
axiom ps : P → S
axiom qs : Q → S


#check (Or.elim porqFromP ps qs)
-- This term, (Or.elim porqFromP ps qs), serves as a proof of S!
```

A little theorem.

```lean
example : P ∨ Q → Q ∨ P
| Or.inl p => Or.inr p
| Or.inr q => Or.inl q
```

Proof:
Assume P ∨ Q is true with a proof, call it h. There are
two cases to consider.
Case 1: P ∨ Q is true because there's a proof, (p : P).
In this case, Or.inr (on the right) is a proof of Q ∨ P.
Case 2: P ∨ Q is true because there's a proof, (q : Q).
In this case, Or.inl (on the left) q is a proof of Q ∨ P.
Those are all the cases for a proof of P ∨ Q, so *whenever*
we're given a proof of P ∨ Q we can derive a proof of Q ∨ P,
so P ∨ Q → Q ∨ P is valid.

### Implication in Lean (→)

#### Introduction

As we've explained, to prove the proposition, P → Q, in
type theory, one must show that there is (one must define)
a total function from P to Q. A total function is one that
works for all values of the argument type.

To make a few more interesting examples, let's recall our
our natural number evenness predicate.

```lean
inductive Ev : Nat → Prop
-- Note: Ev 0 in the following is a proposition
-- ev0 serves as a proof of Ev 0 (which we read as "zero is even")
| ev0 : Ev 0
-- Given n and proof that n is even we can have a proof that n+2 is even
| evFromEv : (n : Nat) → (evn : Ev n) → (Ev (n + 2))
```


The first constructor makes (Ev 0) an axiom by defining ev0
is a proof of it. The second constructor, evFromEv, makes our
second rule defining evenness into an axiom: in this case it is
accepted as a proof of (n : Nat) → (evn : Ev n) → (Ev (n + 2).
As it's a proof of an implication in type theory, it can also
be treated as a function, and as such, when *applied* to an n
and a proof that that n is even, the result is a proof that n+2
is even. We have thus given an *inductive definition* of the
one-place predicate, Ev, representing the mathematical concept
of evenness. It also gives us a nice way to define what we mean
by the infinite set of even numbers: it's the set of just those
numbers, n, for which there are proofs of evenness as we've
just defined it.

A cool observation is that you can't even *apply* evFromEv
to its arguments if n isn't even, because you can never have
a proof that that n is even.

Here are Lean-checked (correct) proofs that 0, 2, 4, and 6 are even.
```lean
open Ev

def zeroEv  : Ev 0 := (Ev.ev0)
def twoEv   : Ev 2 := (evFromEv 0 zeroEv)
def fourEv  : Ev 4 := (evFromEv 2 twoEv)
def sixEv   : Ev 6 := (evFromEv 4 fourEv)
```

Here's a proof of a theorem: if any natural number, n,
is even, then so is n+4. The proof is by two applications
of the inductive step. First from the assumed n and proof
of Ev n, a proof of Ev (n+2) is constructed. Then from n+2
and that latter proof, a proof of n+4 is constructed. QED.


```lean
open Ev
def IfEvNThenEvNPlus4 : (n : Nat) → (Ev n) → Ev (n + 4)
| n, evn => evFromEv (n+2) (evFromEv n evn)
```

Finally, to get back to the main topic of this section,
you prove an implication, such as P → Q, by showing, in
the form of a function of type P → Q, that there is a way
to derive a proof of Q from any proof of P. For example,
the proof we just gave is a function. For any Nat, n, then
from a proof of (Ev n) it *computes* a term that typechecks
as a proof of Ev (n + 2). As long our Ev axioms really do
capture what we mean by evenness then such a proof object
will check as a correct proof that that n is even.

#### Elimination

So how do you use a proof of P → Q, which in Lean is again
in the form of a function, from P → Q? You just *apply* it:
to a specific proof of P to get a proof of Q. As an example,
we proved that if n is even so is (n+4). We actually have a
proof object, called IfEvNThenEvNPlus4. It's a function. If
we apply it to, say, n = 6 and a proof that 6 us even, it
will compute and return a proof that 10 is even!Check it out!

```lean
#check  IfEvNThenEvNPlus4 6 sixEv
--      IfEvNThenEvNPlus4 6 sixEv : Ev (6 + 4) <-- proof Ev 10
```



### Negation (¬)

Recall that at the top of this file we defined F to be a
proposition (type) with no proofs at all. No constructors
means no proofs, as the only proofs of a type are those that
can be constructed using one of the provided constructors.

#### Introduction

Given that F is a proposition with no proofs, we interpret
it as false, and should thus be able to prove that ¬F is true:
that there's a proof of it. Recall that ¬F is defined to be
the proposition F → False, where False is the standard empty
propositional type in Lean. Again the trick to prove ¬F is to
to remember that it simple means F → False.

A proof of that is a proof of an an implication, and in type
theory, that means a function that turns any assumed proof of
F into a proof of False. As we've already reasoned about, it
is possible to define such a function if and only if F is an
uninhabited type. The only trick is that you remember that
to prove ¬F is defined to be identicall to proving F → False.

```lean
def notF : ¬F       -- this is defined to mean F → False
| f => nomatch f    -- assuming a value of type F is absurd
```

#### Introduction: Proof By Negation

So that the introduction rule for negation. To construct a proof
of ¬F it suffices to construct a proof of F → False. Now how should
express this in English? To prove ¬F, assume that F is true, and in
this context you can prove a contradiction (e.g., that False is true).
If you can (and if the logic itself is consistent) the conclusion one
must draw is that F cannot be true in the first place.

Now something quite important: In a traditional paper-and-pencil
discrete math class using first-order logic and set theory, you might
be taught that this form of reasoning is called "proof by contradiction:"
assume F, show False, conclude ¬F. But that is not accurate enough.

Ratherm this form of reasoning, (F → False) ⊢ ¬F, is called *proof by
negation.* To prove a negation, ¬F, it suffices to prove F → False. In
type theory, such a proof is a function, the existence of which proves
that there can be no proofs of F, which is what we mean by F is false,
which is what we mean by ¬F is true.

Summary: We saw in propositional logic that P ⇒ ⊥ ⇒ ¬P. Here in type
theory, we have (F → False) ⊢ ¬F as an axiom: If we have a proof of
F → False, we can conclude (in fact that same proof is a proof of) ¬F.

#### Elimination: Proof by Contradiction

Proof by contradiction is the *elimination* rule for negation. It is
perhaps better remembered as the rule of *double* negation elimination.
In propositional logic, the analog is neg_elim, stating that ¬¬P ⇒ P.
It asserts that you can always eliminate double negations: two nots
cancel out. This statement is clearly valid in PL as it's true in the
underlying Boolean algebra.

This rule embodies the so-called proof strategy of proof by contraction.
In English, we say this: The goal is to prove P. To do this assume ¬P and
show that this assumption leads to a contradiction (e.g., proof of False).
Assuming ¬P and showing False proves ¬¬P. And as long as ¬¬P → P is valid,
that suffices to prove P.

Another way to say this is that if you want to prove P, assume ¬P, show
a contradiction, then conclude ¬P is false, thus ¬¬P must be true, then
by double negation elimination, P must be true. In summary, the axiom of
negation introduction, P → False ⊢ ¬P, defines *proof by negation*, while
the axiom of negation elimination ¬¬P ⊢ P defines proof by *contradiction.*

We've already seen that proof by negation is straightforward in Lean. What
will surely shock you greatly now is to learn that proof by contradiction,
i.e., double negation elimination, *is not an axiom in type theory*. The
axioms of Lean do not include ¬¬P → P as an axiom.

To understand why, you now need to complete the shift in your thinking
from truth-functional (Boolean function) to proof-functional reasoning.
To see that ¬¬P → P is not true in Lean, just suppose you have a proof
of ¬¬P. What you would need to do is to show that from it you can get a
proof of P. But you can't.

To see why, expand the definition of each ¬ connective. Recall ¬P is
defined as P → False. So ¬¬P means ¬(P → False) and this in turn means
(P → False) → False. Just look at this type: it's a function that if
applied to a proof of ¬P would yield of proof of False. The details
don't matter as much as the insight that this proof is a function and
there's no proof of P sitting insider of a function that returns False.

But that's all complicated. Let's think in English. In *classical*
logical reasoning, there are only two possible judgements about any
proposition, P: it's either true or it's false. There is no muddled
middle truth value. In the *constructive* logic of type theory (and
Lean), knowing that ¬P leads to a contradiction doesn't give you a
proof of P, which is what you need to conclude that P is true.

To see in more detail what the issue is, let's just try to prove a
that a statement of neg_elim in Lean is valid and we'll see where we
get stuck. With α being any proposition, we'll try to prove ¬¬α → α.

```lean
example (α : Prop) : ¬¬A → A
| pf => _   -- stuck: need proof of A; only have weird function
```


#### Classical Reasoning

In "classical" logic, such as propositional logic, the
rules of negation elimination, thus proof by contradition,
are valid. In the constructive logic of Lean they're not.
By the term, constructive, we mean that we actually have
to be able to *construct* a proof of a proposition before
we can consider it to be true. The problem with negation
elimination is that we simply can't construct a proof of
a proposition α if all we know is there's no proof of ¬α
(that ¬¬α must be true).

And yet an enourmous amout of mathematics uses proof by
contradiction. Can we not do ordinary mathematics in Lean?
The answer to that is no, that's not what it means. To do
classical reasoning in Lean, you just have to tell Lean
to accept negation elimination as an axiom!

```lean
axiom neg_elim : ∀ {α : Prop}, ¬¬α → α
```


In English that says, Hey Lean. Trust me. You can just
accept that for any proposition, α, if one has a proof of
¬¬α one can simple assume that one can get a proof of α,
and that would be by applying neg_elim!

For example suppose I want to prove P by contradiction
and that I've managed to get a hold of a proof (nnp : ¬¬P).
A proof of P is had by apply negation elimination to nnp.

```lean
axiom nnp : ¬¬P               -- assume I have a proof of ¬¬P
def pfP : P := (neg_elim nnp) -- neg_elim applied to nnp proves P
```

#### Excluded Middle

The main "problem" with negation elimination is that it just
"pretends" that it yields proofs of P from proofs of ¬¬P. A
real proof of P in Lean could be a very complex object, but if
one gets a "pretend" proof of P by applying this axiom, it will
contain none of that detail. No real proof of P is constructed.
We say the axiom of negation elimination is *non-constructive*.

One of the important consequences of the axiom of negation
elimination is that it drives every proposition, P, to be either
true, with a proof (p : P) or false, with a proof (np : ¬P),
with no muddled middle state where one doesn't have a proof
either way. In the preceding example, we could not conclude
that P is true from a proof that ¬P is false, but with the
axiom of negation elimination we can. We can formalize this
statement as another axiom: the so-called law of the excluded
middle.

```lean
axiom excludedMiddle (α : Prop) : P ∨ ¬P
```

Indeed, it turns out that if neg_elim is accepted as an
axiom, then excludedMiddle can be proved, and vice versa!
They are equivalent. It's a litte challenge to prove that!

```lean
def equiv (P : Prop) : ¬¬P ↔ (P ∨ ¬P) := _
```

The proof is left as an exercise!
