# Interpretations

<!-- toc -->

```lean
import DMT1.Lectures.L02_propLogic.formal.utilities
import DMT1.Lectures.L02_propLogic.formal.semantics

namespace DMT1.Lectures.propLogic.semantics

open propLogic.syntax
open propLogic.utilities
```

An interpretation, *i*, in predicate logic is a function
from variables to Booleans;. That is just how we represent
on in Lean: as a value of type Interp, an abbreviation for
the type of total functions from Var to Bool, *Var → Bool*.

Recall that in our specification, a variable expression is
constructed from a variable. All variable expressions built
from the same variable will thus be assigned the same value.

## Defining Interpretations

Suppose for example that we want to evaluate an expression
under an interpretation that assigns the value, *false*, to
every variable, and thus to every variable expressions. We
can define such an interpretation in one line

```lean
private def allFalse : Var → Bool := fun v => false
```

The lambda expression, *fun v => false*, which can also be
written as *λ v => false*, denotes the function that takes
any variable, *v* as an argument and that returns false. The
yellow squiggly line under *v* is Lean warning that we don't
use *v* in the definition of the return value. We can in any
such case remove the argument name, *v*, replacing it with
an underscore, *_*, to specify that we won't be using this
value in the subsequent computation.

In any case, with this interpretation in hand, we can now
evaluate an expression under it. We can use Lean's *reduce*
command to apply *eval* to an expression,, *e*, and to *i*,
to answer the question, does *i* satisfy *e*?

```lean
private def e : Expr := {⟨0⟩}  -- expression on 0th variable
#reduce eval e allFalse        -- expect false
#reduce ⟦(¬e)⟧ allFalse         -- expect true (our notation)
#reduce ⟦(e ∨ ¬e)⟧ allFalse     -- expect true
#reduce ⟦(e ∧ ¬e)⟧ allFalse     -- expect false
```

We can also easily define the all-true interpretation,

```lean
private def allTrue : Interp := λ _ => true   -- _ for don't care
#reduce ⟦e⟧ allTrue            -- expect true
#reduce ⟦(¬e)⟧ allTrue         -- expect false
#reduce ⟦(e ∨ ¬e)⟧ allTrue     -- expect true
#reduce ⟦(e ∧ ¬e)⟧ allTrue     -- expect false
```

Now suppose we want an interpretation for an expression
with two variable sub-expressions. One way to define such
an interpretation function is by case analysis on variable
indices. Here's an interpretation that assigns true to the
0th variable, false to the 1st variable, and true to every
other (irrelevant) variable.

```lean
private def tf : Interp :=
fun v =>
  match v with
  | (Var.mk 0) => true    -- using our abstract syntax
  | ⟨1⟩ => false          -- using Lean's notation for mk
  | _ => true             -- default for all other variables

def f : Expr := {⟨1⟩}
#reduce ⟦(e ∧ f)⟧ tf   -- expect false
#reduce ⟦(e ∨ f)⟧ tf   -- expect true
#reduce ⟦(e ⇒ f)⟧ tf   -- expect false
#reduce ⟦(f ⇒ e)⟧ tf   -- expect true
```

## Generating All Interpretations for an Expression

We we soon be at the point where we'll want to
generate all possible interpretation functions for
any given collection of variables. Given that an
expression with *n* distinct variable expressions
has *2^n* interpretations (ignoring valuations for
variables beyond the range of those appearing in
the expression), it'd be a real chore to have to
write exponential numbers of explicit definitions.

To address this problem, we will define functions
for building interpretation functions from simple
specifications.

For example, we'd like to have a function that takes
any expression, *e*,  and returns a list of all *2^n*
of its possible interpretations. This will enable us
to compute *truth tables* for expressions, where each
interpretation corresponds to one row of a truth table
except for the final output value, which is computed
by applying *eval* to *e** and to the interpretation
that the corresponding row of variable values in the
truth table represents.

The implementation is involves some details. We break
the presentation of our specification of this function
into two parts: all the helpful functions, followed by
the main function of interest. For those looking just
to use this function, you may skip the next section on
the underlying details and jump ahead to the definition
of the "API" that this module provides for end users.

## Helper Functions

One key helper function in our implementation takes
a *list* of Boolean values in positions with indices
from *0* to *n-1* (for an expression, *e*, with *n*
variable expressions), and returns an interpretation
that maps the variable with index *0 ≤ k ⋖ n-1* to the
Boolean value in the *k'th* position in the array of
Boolean values.

We'll build such a final interpretation iteratively,
by starting with an interpretation, e.g., *allFalse*,
then iteratively overriding the value that it assigns
to the *k'th* variable, with k increasing from *0* to
*n-1*. Variables with greater indices are irrelevant
as they do not appear in *e*, and so default to the
values of the interpretation provided as a starting
point (e.g., allFalse).

### Overriding Variable-Value Assignments

The key operation in all of this is overrideBValue, as
defined next. It takes an interpretation function as an
input  along with a variable and a value to be assigned
to that variable, and returns a new interpretation that
is just like the given one except that it now assigns
the specified value to the specified variable. Study
this function with some care. See that the returned
function returns the new value for the variable being
bound to a new value, otherwise the new function just
calls the old function to return the value of any other
variable.

```lean
 private def overrideValue : Interp → Var → Bool → Interp
| i, v, b =>
  λ (v' : Var) =>
    if (v'.index == v.index)  -- if index is variables overridden
        then b                -- return new value
        else (i v')           -- else value under old interp
```

Here's an example. Remember that *e* is a variable
expression build on the variable *(Var.mk 0)* with
index 0. Here we start with *allFalse* and override
it to assign *true* as the value of this variable.
When we evaluate *e* on the resulting interpretation
we'll see that we get the value, true.
```lean
#reduce ⟦e⟧ allFalse                           -- expect false
def newInterp := overrideValue allFalse ⟨0⟩ true  -- override
#reduce ⟦e⟧ newInterp                          -- expect true
```


### Constructing an Interpretation from a List of Bools

With this function value override function in hand, we
can now define a function that takes a list of Bool values
(using Lean's "parametrically polymorphic" List type) and
that returns an interpretation as just described. It works
by passing the number of variable values to be overridden
(the length of the list of Bools) and that list to a helper
function that takes the number of variable values  and this
list and that uses recursion to iteratively override variable
*k* with the corresponding list entry.

Note that the helpder function is defined by cases that match
on two arguments. The first pattern matches when the list of
Booleans to assign is empty, in which case this function just
returns the *allFalse* interpretation. Otherwise, if the number
of variables to bind is non-zero, and the list of values has
*h* (for *head* of list) as its first value and *t* (for *tail*)
as the rest of the list), then it overrides the value of the
next variable with that value at the head of this list. It may
be possible to improve this definition. If you do that, please
send a pull request.
```lean
private def interpFromBools : List Bool → Interp
  | l => boolListToInterp l.length l
where boolListToInterp : (vars : Nat) → (vals : List Bool) → Interp
  | _, [] => (λ _ => false)
  | vars, h::t =>
    let len := (h::t).length
    overrideValue
      (boolListToInterp vars t)
      (Var.mk (vars - len)) h
```

Here's an example, where nextInterp assigns true to
the variable with index *0* (and thus as the value it
assigns to *e*), false to the variable with index *1*,
and then false to every variable at any higher index.
```lean
def nextInterp : Interp := interpFromBools [true, false]
#eval ⟦e⟧ nextInterp    -- expect e to evaluate to true
```

### Nth Interpretation for Expression With k Variables

A key insight behind our design is that each row of a
truth table (without the final column containing the
value of the expression) represents an interpretation.
Moreover, the Boolean values in each row can be made to
correspond to the Boolean digits (bits) in the binary
expansion of the row index.

For example, if *e* includes two variable expressions,
it will have four rows with indices from *0* to *3*,
with binary expansions of 00, 01, 10, 11. The bits in
each of these numerals are exactly the Boolean values
to be assigned to each of the two variables by each of
the respective interpretations.

The following function uses these observations to take
a row index and the number of variables in an expression
and return an interpretation corresponding to that row.
It works by obtaining a list of Booleans for the indexed
row (computed by another helper function) and converting
it to an interpretation as described above.

```lean
private def interpFromRowNumVars : (nth: Nat) → (numVars: Nat) → Interp
| index, vars =>
  interpFromBools
    (listBoolFromRowIndexForNumVars index vars)
```


### All Interpretations for Expression With k Variables

The next function takes a number of variables in an expression
and returns a list of all 2^n interpretations for that number
of variables. Be careful as the size of the constsructed list
is exponential in length in the number of variables.

```lean
private def interpsFromNumVars (numVars : Nat) : List Interp :=
  mk_interps_helper (2^numVars) numVars
where mk_interps_helper : (rows : Nat) → (numvars : Nat) → List Interp
  | 0,        _  => []
  | (n' + 1), v  => (interpFromRowNumVars n' v)::(mk_interps_helper n' v)
```

### Printable Representation for Interpretation Functions

Next we define two helper functions, available for use
by clients of this module, for mapping an interpretation (which
as a function is unprintable) to printable forms, namely to a
list of 0/1 natural numbers reflecting the values assigned to
the variables with corresponding indices.

```lean
private def bitListFromInterpHelper : (i : Interp) → (w : Nat) → List Bool
| _, 0 => []
| i, (w' + 1) => bitListFromInterpHelper i w' ++ [(i ⟨w'⟩)]  -- ++ is List.append

#reduce bitListFromInterpHelper allFalse 3 -- expect [0, 0, 0]
```

This function takes any list of interpretations and returns
a list of bit lists, one for each of the interpretation.
```lean
private def bitListsFromInterpsHelper : List Interp → Nat → List (List Bool)
| [], _ => []
| h::t, n => bitListFromInterpHelper h n::bitListsFromInterpsHelper t n
```

Lean knows how to print lists of natural numbers, and lists
of lists of natural numbers, so these functions can be used
to derive printable forms of interpretation and lists thereof.
Remember that an interpretation in our design binds values to
an infinite number of variables, of which only a finite initial
sub-list of variable-to-value bindings is relevant. We provide
the number of *relevant* variable bindings for which outputs
should be generated as the second argument to this function.

```lean
#reduce bitListsFromInterpsHelper (interpsFromNumVars 3) 3
```

By can ask for bindings for more variables than are relevant,
and in this case, we'll get default values from the initial
interpretation that was overriden with new values for all of
the relevant (first *n*) variables. Here, we started with the
*allFalse* interpretation, so the values beyond the three that
we care about in this example will be false. These values are
ignored during evaluation and so are irrelevant and should be
considered as an implementation detail in our design.

```lean
#reduce bitListsFromInterpsHelper (interpsFromNumVars 3) 5
```

### Counting the Number of Variables in an Expression

To compute a list of all interpretations for  given expression,
*e*, we just need to know the number of variable expressions in
*e*. That number, in turn, is one more than the highest variable
index value for an variable used in a variable expression in *e*.
As examples, the answer for *P ∧ P* would be *1*; for *⊤* it'd be
*0*, as there are no variable expressions in the expression, *⊤*.

This function definition provides a nice example of case analysis
on the structure of the expression argument, *e*. If it's a literal
expression, the answer is *0*. If it's a variable expression built
from the variable (Var) with index i, the answer is *i + 1*. For a
unary operator expression, *(op e)*, it's the number of variables
in *e*. And for a binary operator expression, *(op e1 e2)* it's
the maximum of the number of variables in each of *e1* and *e2*.
```lean
private def numVarsFromExpr : Expr → Nat :=
  (fun e => maxVariableIndex e + 1) where
maxVariableIndex : Expr → Nat
| Expr.lit_expr _ => 0
| Expr.var_expr (Var.mk i) => i
| Expr.un_op_expr _ e => maxVariableIndex e
| Expr.bin_op_expr _ e1 e2 => max (maxVariableIndex e1) (maxVariableIndex e2)
```

## API: Get List of All Interprations for Expression

Given a Expr, *e*, return a list of all of its *2^n*
interpretations in *ascending* order (from all-false to
all-true). This function works by computing a list of
all interpretations for *n* variables where *n* is the
number of variables in *e*.
```lean
def interpsFromExpr : Expr → List Interp
| e => interpsFromNumVars (numVarsFromExpr e)
```

In addition we provide public versions of the functions
for deriving printable representations of interpretations.
```lean
def boolListFromInterp :=  bitListFromInterpHelper
def boolListsFromInterps :=  bitListsFromInterpsHelper

-- Example
def anExpr := ({⟨0⟩} ∧ {⟨1⟩} ∨ {⟨2⟩})  -- P ∧ Q ∨ R
#reduce boolListsFromInterps (interpsFromExpr anExpr) 3
```


As a final note, if you improve this module's
implementation, please send me a pull request!

```lean
end DMT1.Lectures.propLogic.semantics
```
