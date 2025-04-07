# Examples

<!-- toc -->



The material in this chapter depends on our specification
of the syntax of propositional logic. We enclose these
definitions in a namespace, DMT1.lecture.propLogic.axioms,
to avoid naming conflicts with definitions in other files.
We open the namespace for both the syntax definitions and
the specification of the syntax itself (Expr), so as to be
able to use them here without prefixes.

```lean
import DMT1.Lectures.L02_propLogic.formal.syntax

namespace DMT1.Lectures.propLogic.axioms

open propLogic.syntax

open Expr
```



## Variable Expressions

It'll suffice for our purposes to have three variable
expressions. We'll call them P, Q, and R. The following
definitions provide them, built on the variables indexed
by 0, 1, and 2, resp. See our concrete syntax definitions.

Note that the first example of a definition of a *variable
expression* is written entirely using abstract syntax. We
apply *Var.mk* to the natural number index, 0, to create a
*Var* object that we then use to build a variable expression
by giving it as an argument to the Expr constructor used to
build variable expressions. The next two examples use our
concrete notations. Note: the expression, (Var.mk 1), uses
parentheses, while the expression ⟨2⟩ uses angle brackets.
Look closely. Lean provides this angle bracket notation as
a shorthand for applying the "mk" constructor of a structure
type to its arguments.

```lean
def P : Expr := var_expr (Var.mk 0)   -- Lean abstract syntax
def Q : Expr := var_expr ⟨1⟩          -- Lean concrete: Var.mk 1
def R : Expr := {⟨2⟩}                 -- Our concrete: Expr.var_expr ...
```



## Operator Expressions

Now that we have a few elementary expressions
(we can call them propositions) we present a set
of propositions that turn out to be important. For
now, they're just examples of syntactically correct
expressions in the syntax of our little language.

```lean
def and_intro :=        R ⇒ Q ⇒ R ∧ Q
def and_elim_left :=    R ∧ Q ⇒ R
def and_elim_right :=   R ∧ Q ⇒ Q

def or_intro_left :=    R ⇒ R ∨ Q
def or_intro_right :=   Q ⇒ R ∨ Q
def or_elim :=          Q ∨ R ⇒ (Q ⇒ P) ⇒ (R ⇒ P) ⇒ P

def not_intro :=        (R ⇒ ⊥) ⇒ ¬R
def not_elim :=         ¬¬R ⇒ R

def imp_intro :=        R ⇒ P ⇒ (R ⇒ P)
def imp_elim :=         (R ⇒ P) ⇒ R ⇒ P

def equiv_intro :=      (R ⇒ P) ⇒ (P ⇒ R) ⇒ (R ↔ P)
def equiv_elim_left :=  (R ↔ P) ⇒ (R ⇒ P)
def equiv_elim_right := (R ↔ P) ⇒ (P ⇒ R)

def true_intro := ⊤
def false_elim := ⊥ ⇒ P
```

As we'll later, this is not a collection of arbitrary
propositions (expressions), but of propositions that
we can take as defining a set of elementary principles
for valid reasoning. For now, though, we can take them
as good examples of expressions we can write now using
the syntax we've defined.

```lean
end DMT1.Lectures.propLogic.axioms
```
