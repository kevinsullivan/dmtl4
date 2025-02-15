Semantic Validity

UNDER CONSTSRUCTION

# Validity

<!-- toc -->

Validity is an incredibly important property to understand.
Whether is propositional or some other logic, an expression is
said to be valid if it's *always* true, which is to say it's
true in all possible worlds, independent of choice of domain,
and of interpretations into any domain.

A domain where validity is absolutely central is mathematics.
A *theorem* is a proposition in a formal language for which
there is a proof that it is valid. We will often say informally
that a theorem has been proven to be true. What we mean by that
the proposition is true in all of the possible worlds to which
the elements of the proposition might refer.

## Semantic Validity for Propositional Logic

At this point, we've established a definition of what it means
for a proposition in propositional logic to be valid: that it
is true under all possible intepretations: in all possible world
states, as it were.

## Predicate Logic Changes the Game

In the next unit of this class, we will meet a much more
expressive logic: namely predicate logic. This is the language
of the working mathematician, software specifier, symbolic AI
coder, and many others.

### The Domain is Variable

Predicate logic is far more expressive language in several
ways. First, its semantic domain is now a variable. In order
to evaluate the truth of a proposition, the domain must be
defined, along with an interpretation of variables as objects
in the selected domain.

### It has Existential and Universal Quantifier Expressions
In addition, predicate logic extends the propositional logic
with universall and existential quantifier expressions, of the
formm, *∀ (x : α), P x* and *∃ (x : α), P x*. The first can be
read as, every *x* of type *α satisfies the predicate, P; and
the latter, as "some (at least one) x satisfies P."

### It has Predicates: Abstractions from Families of Propositions

A predicate, in turn, is parameterized proposition. It's
a proposition with some remaining blanks to be filled in.
We will represent predicates as functions. One applies a
predicate to an argument to fill in the blanks where that
choice of value is required.

Here's an example. I propositional logic, I could define
three propositions, *TomIsHappy*, *MaryIsHappy*, and
*MindyIsHappy*. There is way in propositional logic to
*abstract* from this family of apparently close related
propositions to a single predicate, *XIsHappy*, where
*X* is a parameter. Now applying *XIsHappy* to a
particular person, *Ben*, would reduce to the proposition,
no longer a predicate, that *BenIsHappy,* as a special case.

### Validity is No Longer Semantically Definable

In propositional logic, there's just one semantic domain,
Boolean algebra, and only two semantic values to which
variable expressions can be referred by an interpretation.
Expressions, as values of an inductive type, are always
finite in size, so there can only be a finite number of
variable expressions in any given larger expressions, so
there is always a finite number of interpretations for
an expression in propositional logic. We can thus decide
whether any proposition is valid algorithmically (which
means with an always finite computation).

That is no longer the case when we get to predicate logic.
There's now an unbounded number of possible domains. You
can se predicate logic to talk about anything. Predicate
logic is a "bring your own domain" formal language! Such
domains need not be finite (e.g., we can take real= numbers
as a values to which some variable expressions refer. Or
the same expression might be interpreted as asserting that
some condition is true of traffic in Boston. Cearly we can
no longer test an expression for validity by evaluating it
under a finite number of interprtations.

How can we show that a given proposition is true for every
possible interpretation (every possible world state) in
every possible domain? We need something different.
