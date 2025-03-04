```lean
/-!
# Boolean Algebra

<!-- toc -->

The semantic domain in propositional logic is
Boolean algebra. An algebra, such as Boolean algebra,
generally involves one or several kinds of objects,
operations to construct objects of these kinds, and
operations that use objects of these kinds to derive
other objects/values. For example, addition uses two
Nat values to construct a third, the result.

Boolean algbra includes
- a type of Boolean values: true, false
- unary and binary Bool-consuming operators

Lean already provides most of the elements  of Boolean
algebra that we need to serve as a semantic domain for our
definition of propositional logic: the Bool type and the
most commonly used Booolean operators as functions.

The two elements we'll need that Lean doesn't define
natively are definitions of *implies* and *equivalentTo*.
-/

namespace DMT1.Lectures.propLogic.semantics.domain

/-
## Lean's Boolean Algebra Definitions

The standard Lean libraries define the Boolean
Type, the Boolean operators (functions) commonly
used in programming (&&, ||, !).
```

#check true && (true || !true)


```lean
## Implication

Suppose you have an implication expression, say
*P → C*. There are two useful but distinct ways
of working with implications.

A reading in the forward asserts that if you know
*P* to be true, in some situation, then you can
safely conclude that *Q* must also be true.  In
the reverse direction, it explains that for *Q*
to be true it suffices for *P* to be.

The first reading suggests that if you know *P → Q*
and *P* are both true, then *Q* must be as well. So
it propagates a truth judgment from *P* to *Q*. The
second perspective is important if your *goal* is to
show that *Q* is true, because if you also know that
*P → Q* is true, then you can replace *Q* with *P* as
your new goal. We develop this perspective thoroughly
when we get to predicate logic and deductive reasoning.

#### Missing Boolean functionss
But
it doesn't define all the ones we need, including the
likes of implies and iff. In other words, Lean doesn't
give us a complete enough specification of the semantic
domain of Boolean algebra. So in this file, we'll just
define the rest of what we need. For now, that means
binary Boolean functions for *implies* and *iff*.


For now, all we need to do is to have definitions of
functions that implement the truth tables of the Boolean
→ and ↔ operators. Each function, taking two Boolean
arguments, is defined "by cases", of which there are
four. In other words, we're specifying truth tables.
-/

-- Implication
def imp : Bool → Bool → Bool
| true, true => true
| true, false => false
| false, true => true
| false, false => true
```


First: *(P → Q) → (Q → P) → (P ↔ Q)*.
Then, *(P ↔ Q) → P → Q*
and *(P ↔ Q) → Q → P*

```lean
-- Equivalence (bi-conditional, if and only if)
def iff : Bool → Bool → Bool
| true, true => true
| false, false => true
| _, _ => false

-- Problem #1 (combinatorics): How many binary Boolean functions are there?
-- Problem #2 (Boolean algebra): Write a specification of the exclusive or function (xor)
```

## Conclusion

Boolean algebra comprises the set of two Boolean values
along with the collection of functions from Booleans to
Boolean values. These functions include negation (unary),
conjunction, implication. These objects, both values and
functions, are *denotations* of propositional logic syntax
elements: of constants and variables and of the syntactic
operators, such as ∧ (mapping to &&).

```lean
end DMT1.Lectures.propLogic.semantics.domain
```
