# Syntax

This chapter presents our formal definition of the
syntax propositional logic.

<!-- toc -->

We import the theory syntactic language
```lean
import DMT1.Lectures.L04_natArithmetic.syntax

namespace DMT1.Lectures.theoryExtensions.syntax
```



The syntax specifies the set of all and only syntactically
correct propositional logic expressions. Roughly speaking,
the syntax defines "literal" and "variable" expressions and
a collection of expression-composiing operators that take
smaller expressions as arguments to yield larger expressions
as results.

- literal expressions
- variable expressions
- operator (application) expressions

Remember: we're not talking about Boolean meanings of
literals, variables, or bigger expressions here. The
syntax of a formal languages defines only the set of
syntactically correct expressions in our language and
says nothing about their intended meanings.

Now what's interesting is that we formalized the set of
all correct expressions as Expr. It's a data type. Now
any particular logical expression is just a value of this
Expr type. The available constructors describe all all
and only the ways to construct a term of this type. Lean
automatically checks the correctness of terms declared to
be of this type. The Lean type checker thus now provides
us with a syntax checker for propositional logic.

Let's dive down into literal, variable, and application
(operator application, if you want) expressions and how
we represent them in Lean.

### Literal Expressions

The term *literal expression* refers to an expression
that directly names a value. In propositional logic the
two values of interest are the Boolean values, *true*
and *false*.

Our implementation of propositional logic thus defines
two literal expressions, each built by applying the
expression constructor called *lit* to one the two
Boolean values (Bool.true or Bool.false). Our language
will thus include (lit true) and (lit false) as its two
literal expressions. In logical writing it's common to
use the *concrete* syntactic symbols ⊤ (pronounced "top"),
as a notation   for (lit true), and ⊥ (pronounced "bottom")
for the expression (lit false).

### Variable Expressions

Variable expressions are a little more complicated, but
not much. Just as a lit expression is built from a Boolean
value (and incorporated as a value into the resulting term),
a variable expression is built from a variable (a value of
a type we'll call var). Each var object in turn is built
from a natural number (0, 1, 2, ...). The natural number
in one var distinguishes that var from any var having a
different natural number "index." This design provides us
as future authors of masterpieces in propositional logic
an infinite supply of distinct variables to use in writing
our logical opus magni. So, again, lets dig down a little
more.

#### Variables

We define *var* to be the type of *variables* as we've
been using the term: they are not themselves expressions
but are necessary values for making variable expressions.


### Variables

We will now have both Boolean and arithmetic
(Nat-valued) variables, from which we will then
be able to build variable expressions.

```lean
structure LogicVar : Type where
  mk :: (index: Nat)
deriving Repr
```



Lean detail: If you omit a constructor name,
Lean uses *mk* by default.

```lean
structure ArithVar : Type where
  (index: Nat)
deriving Repr

-- See: it's defined
#check ArithVar.mk
```




##### Concrete syntax for variables (var)

We could define our own concrete notation for variables,
but Lean provides one automatically for any "structure"
type. A structure type has exactly one constructor. You
can give it a name, but Lean defines *mk* as the default.
This constructor will take zero or more argument. So, to
build a value of such a type you can use ⟨ a, b, c,... ⟩
notation as a shorthand for, say, "var.mk a b c ....".
We do need to let Lean know the result show be a "var".
```lean
#check (⟨3⟩ : LogicVar)    -- it's a variable (var)
-- #check ⟨3⟩             -- not unique constructor expr
-- But where Lean can infer Var type ⟨3⟩ will suffice
```


Now we just defined variables expressions as expressions
of the form (var_expr v). We define var_expr shortly. View
var_expr as the method for constructing a variable expression
from a variable. ANd given a variable expression, you can
get the underlying variable back out to work with. We'll
need that when it comes to defining interpretations as
functions that take *variables* in and that return values
from the semantic domain, here just of Boolean values.




### Operator Expressions

Next we define the *expression-composing operator* (also
called *connectives*) of propositional logic. Each such
operator takes at least one expression as an argument and
uses it in constructing a larger expression.

- applying the *not* operator to an expression e yields the expression (not e)
- applying a *binary* operator, op, to e1 and e2, yields the expression (op e1 e2)
- here, op can be and, or, not, implies, iff, and so forth

We call the only unary operator *not*, and the usual binary operators
by their usual names. Remeber, these are meaningless symbols in the formal
*syntax* of propositional logic. We give them names that will reflect their
usual meanings when we define *semantics* for syntact expressions.

```lean
-- unary connective (syntactic expression composers)
inductive UnOp : Type
| not
deriving Repr

-- binary connectives (syntactic expression composers)
inductive BinOp : Type
| and
| or
| imp
| iff
deriving Repr
```

Now we get to the heart of the matter. With those preliminary
dependencies out of the way, we now formally specify the complete
(abstract) syntax of propositional logic. We do this by defining
yet another data type. The idea is that values of this type will
be (really will represent) expressions in propositional logic. In
fact, in Lean, this type specifies the set of *all* and *only*
the expressions legal in propositional logic.

### Syntax of Propositional Logic with Arithmetic

```lean
inductive Expr : Type
| lit_expr (from_bool : Bool) : Expr
| var_expr (from_var : LogicVar)
| un_op_expr (op : UnOp) (e : Expr)
| bin_op_expr (op : BinOp) (e1 e2 : Expr)
| arith_pred_expr (from_pred : natArithmetic.syntax.PredExpr)
deriving Repr

#check Expr.arith_pred_expr
```

Every type encloses the names of its constructors
in a snamespace with the same name as the type. So
Expr is now a namespace, and the constructor names
(lit_expr, etc.) are referred to as Expr.lit_expr,
etc. To avoid having to repeat that Expr. bit all
the time, one can "open" the namespace. Just don't
do this if it would result in names having multiple
different definitions being "directly visible."
```lean
open Expr
```



## Concrete Syntax: All the Usual Notations

A well designed, user tested, concrete syntax for a
given formal language can be a huge aid to the human
of abstract formal definitions in that language. We
prefer to write (3 + 4) over (add 3 4), for example.
We don't expect you to have justifiable confidence
in your deep understanding of this notation stuff at
this point! We encourge you to follow it carefully
to get the gist.

```lean
-- (lit true) and (lit false) expressions
-- a variable expression constructed from from a variable

-- our single unary connective, *not* (¬)
-- we set it to have maximum precedence (binding strength)
```

Here are concrete notations for our binary connectives.
The letter "l" after infix specifies left associativity.
The numbers after the colons specify binding strengths.
The de-sugared versions follow after the arrows.

```lean
notation:max " ⊤ " => (Expr.lit_expr true)
notation:max " ⊥ " => (lit_expr false)
notation:max "{" v "}" => (var_expr v)
notation:max "⟨" e "⟩ " => arith_pred_expr (e : natArithmetic.syntax.PredExpr)
notation:max "¬" p:40 =>  un_op_expr UnOp.not p
infixr:35 " ∧ "  =>       bin_op_expr BinOp.and
infixr:30 " ∨  "  =>      bin_op_expr BinOp.or
infixr:20 " ↔ " =>        bin_op_expr BinOp.iff
infixr:25 " ⇒ " =>        bin_op_expr BinOp.imp
```

That's it. That's the entire abstract and concrete
syntax for predicate logic. Note that some definitions
of the syntax of propositional logic do not include the
literal expressions, ⊤ and ⊥. In that case one will just
use variable expressions instead, taking care to fix the
interpretations of these variables as unvaryingly either
true or false.

```lean
end DMT1.Lectures.theoryExtensions.syntax
```
