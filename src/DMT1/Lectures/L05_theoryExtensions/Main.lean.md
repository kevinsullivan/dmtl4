```lean
import DMT1.Library.propLogicWithArith.semantics

open DMT1.natArithmetic.syntax


/-
# Propositional Logic with Nat Arithmetic as a Theory Extension

Our aim is to work up to a demonstration of the construction of
expressions in our new and more *expressive* logic: propositional
logic with natural number arithmetic as a theory extension. That
means we can now write propositional logic expressions that have
arithmetic *relational* (Boolean-valued!) expressions in natural
number arithmetic. Let's start from the bottom up.
-/


/-!
## Language of Arithmetic
-/


/-!
### Arithmetic variables

As a reminder, arithmetic variables in our design will serve
both as building blocks of arithmetic *variable expressions*,
and as arguments to interpretation functions, each of which in
turn associates (maps) variables with (to) mathematical domain
values (e.g., Boolean or natural number values).
-/
-- arithmetic *variables*: indexed by natural numbers
def v0 : DMT1.natArithmetic.syntax.Var := Var.mk 0   -- abstract syntax
-- Not that Var in this context means natArithmetic.syntax.Var. See why for yourself.
def v1 : Var := ⟨ 1 ⟩      -- concrete syntax: see natArithmetic syntax file
def v2 : Var := ⟨ 2 ⟩      -- the 0, 1, 2 here are variable *indices* not values!


/-!
### Variable indices are syntactic: not variables' semantic domains values
It's really important that you not confuse the natural
number *indices* of *variables* with the values that we will
assign to them. The values of these variables will be defined
by interpretations. Different interpretations associate different
natural number values with given *variables*.

It's just as important that you distinguish variables from variable
expressions. Variable expressions are expressions in the language of
natural number arithmetic that we're definining. Each *expression*
is constructed from a *variable.
-/


/-!
### Arithmetic *variable expressions* in the language of arithmetic
-/
-- *variable expressions*, each constructed from a distinct *variable*
def M := DMT1.natArithmetic.syntax.Expr.var v0  -- abstract syntax
def N := { v1 }       -- concrete syntax: see natArithmetic.syntax.Expr
def P := { v2 }


/-!
### Arithemtic operator expressions.
-/

/-!
And now that we have a few small *expressions* in hand (the variable
expressions M, N, and P) we can form even larger *expressions* using
available *operators*. Here's an example of a larger expression built
from a smaller one using the "+" operator.
-/

def e1 := N + M

/-!
It's crucially important to understand that we have not yet assigned
natural number values or mneaning to any of the the variables, variable
expressions, or operators that we've defined and used here. It's the role
of *semantics* to assign meanings to such syntactic elements.
-/

open DMT1.natArithmetic.semantics


/-!
### Interpretations of *arithemtic* variables

Here's one possible interpretation (*function* fron variables to values).
The variable with index 0 is associated with the value, 2, etc. Be
sure you understand that an "Interp" is a *function* from *variables*
to values. There can be many different functions of this type.
-/

def i1 : Interp   -- see definition of natArithmetic.semantics.Interp
| Var.mk 0 => 2
| Var.mk 1 => 3
| Var.mk 2 => 5
| _ => 0

-- another possible interpretation: every variable's "value" is 0
def i2 : Interp
| _ => 0          -- v matches *any* variable

-- and one more interpretation
def i3 : Interp
| Var.mk 0 => 1
| Var.mk 1 => 10
| Var.mk 2 => 100
| _ => 0

/-
### Evalation of *arithemtic variables* under interpretations
Now we have a set-up where different interpretation functions
associate different values with different variables. Here we are
applying interpretation functions to variables.
-/

#reduce i1 v0   -- expect 2
#reduce i1 v1   -- expect 3
#reduce i1 v2   -- expect 5

/-!
### Evaluation of *arithmetic variable expressions*
Remember: variables are not variable *expressions*. The latter are
elements in our language, each of which "contains" (is constructed
from) a variable. To evaluate a variable *expression* we apply our
*expression* evaluation function (here called eval). Here we
evaluate the same *expression* using our different interpretations.
-/

-- Examples: evaluating variable expressions
-- DMT1.natArithmetic.semantics.eval
#reduce eval M i1
#reduce eval M i2
#reduce eval M i3

-- Examples: evaluating operator expressions
#reduce eval e1 i1    -- DMT1.natArithmetic.semantics.eval
#reduce eval e1 i2
#reduce eval e1 i3

def e4 : Expr := sorry + sorry  -- the arguments can by any *expressions*
def e4' : Expr := (M + N) + P
def e4'' : Expr :=
  Expr.binOp                  -- bin op expr
    BinOp.add                 -- op = +
      (Expr.binOp               -- e1 = (M + N)
        BinOp.add                 -- (op = +
        (Expr.var (Var.mk 0))     --  e1 = M
        (Expr.var (Var.mk 1)))    --  e2 = N
      (Expr.var (Var.mk 2))     -- e2 = P

/-!
### Arithmetic Relational Expressions: Syntax

You should now be able to understand
our syntax for *relational* expressions.

Its formal specification of the syntax of
our language is given by RelExpr. Speaking
informally, the syntax has only one form
of expression, namely "l op r", where op
is a relational operator (such as ≤), and
l and r are *arithmetic* expressions. An
example in the ordinary language of sixth
grade math: 3 < X: There is an arithmetic
literal expression on the left, variable
expresion on the right, and the relational
operator in the middle (infix notation).
-/

def r1 := (M ≤ [20])  -- var_expr op lit_expr
def r1' :=            -- its abstract syntax
  RelExpr.mk
    RelOp.le                -- ≤
    (Expr.var (Var.mk 0))     -- M
    (Expr.lit 20)             -- 20

def r2 : RelExpr := (M > N)

/-
### Arithmetic Relational Expressions: Semantic Evaluation
Sematic evaluation of *arithmetic relational
expressions*, yielding Boolean values. This is
why we can integrate these arithmetic expressions
smoothly into propositional logic. Like PL variables
they, too, evaluate to Boolean values.
-/

-- evalating relational expressions under varying interpretations

#eval evalRelExpr r1 i1 -- 10 < 20, expect true
#eval evalRelExpr r1 i2
#eval evalRelExpr r1 i3

#eval evalRelExpr r2 i1
#eval evalRelExpr r2 i2
#eval evalRelExpr
        r2
        i3

#eval evalRelExpr       -- expect false
        ((M + N) > (N + M))
        i3

#eval evalRelExpr         -- expect false
        ([20] ≥ (N * P))  -- relational expression
        i3                -- arithmetic variable interpretation

/-!
### Summary: A Formal Language of Natural Number Arithmetic

O. M. Gosh, Yay. We now have a working formal specification
of a little expression language of natural number arithmetic.

Our specification defines both syntax (the Expr and RelExpr)
types, and an operational semantics (the evalPLAExpr function).
Given *any* expression and *any* variable interpretation, this
function actually "operates (works!)" to compute the meaning /
valye of the expression given an added interpretation function.
That's why we call it an "operational" semantics.

A hypothetical user of our little expression language would
generally want to write numerical and relational expression
using our concrete syntax, rather than using abstract syntax.

But you are not just a language user but a language designer!
In this capacity, you really must understand how expressions
using concrete syntax get "desugared" into abstract syntactic
expression. See the example, def e4' : Expr := (M + N) + P, a
few paragraphs back.
-/

/-!
## Propositional Logic with Nat Arithmetic as a Theory Extension
-/

/-!
And now for the syntax and operational semantics of our own
verson of proposition logic with our own language of arithmetic
relational expressions as a theory extension. Moreover we now
have sophisticated computational tools to rigorously enforce
the syntax rules of the language (that only certain constructs
are allowed) and to evaluate the truth of propositional logic
expressions with arithmetic relational operators expressions
as a new basic construct. The key to smooth integration is
that, just like propositional logic variables and variable
expressions, these *arithmetical relational* expressions *also
evaluate to Boolean values*.

So here we go. Let's see how we've incorporated arithmetic
relational operator expressions as new basic expressions in
an extended version of propositional logic.

A note. The definitions in the Library duplicate rather than
include syntax, semantics, and domain from Library/propLogic.
This makes the definitions more self-contained for purposes
of presentation.
-/

open DMT1.propLogicWithArith.syntax
open DMT1.propLogicwithArith.semantics

/-!
### PLA Relational Operator Expressions (Syntax)
Now we construct some expressions in propositional logic
with arithmetic, constructing each one from an underlying
arithmetic relational operator expression in our language
of natural number arithmetic.

Just as we build PL variable *expressions* from variables,
so we will construct PLA relational arithmetic expressions
(in the PLA language) from from arithmetic expressions (in
the language of natural number arithmetic).

To quickly understand the construction of a propositional
logic expression, that can be used in building larger such
expressions, from an arithmetical relational expression, it
is best to draw an analogy with our method of constructing
a variable expression (an expression in propositional logic)
from a variable (not an expression in propositional logic).
Now we're analogously
-/

#check (PLAExpr.rel_op_expr ([7] ≤ [8]))

#reduce evalPLAExpr (PLAExpr.rel_op_expr ([7] ≤ [8])) _ _

#eval evalRelExpr
        ([9] ≤ [8])
        (fun _ => 0)

/-!
### Constructing PL Relational Expressions: Concrete Syntax

At the moment we've used only abstract syntax for building
*propositional logic* (relational operator) expressions from
arithmetic relational expressions. We've also defined a new
concrete syntax, employing the same pattern as used to turn
a variable, v, into a variable expression: { v }. Similarly
we can now turn anarithmetic relational expressions, r, into
a propositional logic (relational operator) expression using
{ r }.
-/

/-!
### Examples of PLA Expressions

A *propositional logic (with arithmetic) expression*
constructed from an *arithmetic relational expression*.
The arithmetical relational expression is constructed
from two arithmetic literal expressions and a relational
operator, ≤. The application of PLAExpr.rel_op_expr to
this arithmetic relational expression "boxes it up" and
the result is now an expression in propositional logic
with arithmetic.
-/
def pla1 : PLAExpr := PLAExpr.rel_op_expr ([7] ≤ [8])

/-!
As an expression in propostional logic (with arithmetic)
its truth can be determined by propositional logic (with
arithmetic) evaluation. The semantic evaluation function
for this language requires *two* interpretation arguments,
one to assign values to propositional logic variables, the
other to assign values to aritmetic variables. Here we use
"function expressions" in Lean to provide trivial examples
of interpretations (every logic variable is mapped to false
and every numberic variable is mapped to zero).
-/

#eval evalPLAExpr pla1 (fun _ => false) (fun _ => 0)

-- What if we reverse the literals? Now
#eval evalPLAExpr                         -- PLA sem eval
        (PLAExpr.rel_op_expr ([6] ≤ [7])) -- PLA expression
        (fun _ => false)                  -- PL/Bool interp
        (λ _ => 0)                        -- Arith interp (λ = fun)


/-
It quickly becomes apparent that constructing PLA expressions
without good concrete syntax is unnecessarily burdensome and
produces "code" that's hard to read. We need a nice concrete
syntax. As building PLA expressions from arithmetic relational
expression is analogous to building variable expressions from
variables, and to maintain systactic consistency, I decided to
use the same concrete syntax, namely "{" r "}", where r is any
arithmetic relational expression.
-/


def pla2 : PLAExpr := {[7] + P ≤ [8]}   -- that's better!

/-!
And now the *coup de grace*: We can use logical connectives to
build larger "propositional logic with arithmetic" expressions
(PLAExpr values) from smaller ones using all the usual logical
connectives, *and* we can evaluate the truth of any expression
of this kind, given two interpretations, that serve to associate
values with respectively propositional arithmetic variables (and
thus to variable expressions in both languages).
-/
def pla3 : PLAExpr := pla1 ∧ pla2

/-!
### Propositional Logic with Arithmetic: Semantic Evaluation

Here's a copy of our formal specification of an operational
semantics for our formal language of propositional logic with
arithmetic. As an important exercise, you should now express
each rule in English. There's an intricate little dance going
on here, with tbe evaluation of propositional logic expressions
using the evaluation of *arithmetic* relational expressions,
yielding Boolean values, as a subroutine.

def evalPLAExpr : PLAExpr → Interp → ArithInterp → Bool
| (PLAExpr.lit_expr b),             _, _ => b
| (PLAExpr.var_expr v),           i, _ => i v
| (PLAExpr.un_op_expr op e),      i, a => (evalUnOp op) (evalPLAExpr e i a)
| (PLAExpr.bin_op_expr op e1 e2), i, a => (evalBinOp op) (evalPLAExpr e1 i a) (evalPLAExpr e2 i a)
| (PLAExpr.rel_op_expr re),       _, a => (natArithmetic.semantics.evalRelExpr re a)

### Examples: Semantic Evaluation of Expressions in PLA

As a quick reminder, our semantic evaluator for PLA expressions
(propositions in the language of PLA) takes an expressions and
*two* interpretation functions. The first will take Vars as
arguments and return Boolean values. The second will take Vars
(sorry, imperfect name) as defined in the natArithmetic library
and return natural numbers. So let's get on to the examples.

You are responsible for understanding all aspects of the syntax
and the semantics of this language, including how exactly semantic
evaluation is carried out, including but not limited to the roles
of the two interpretation arguments in enabling the reduction of
expressions to their meanings as values from a semantic domain.
-/

-- predict the answer before you check
#eval evalPLAExpr
        pla3            -- delta reduction
        (fun _ => false)  -- no propositional variables in pla3: placeholder
        i2              -- all-zero arithmetic interpretation from above

-- predict the answer before you check
#eval evalPLAExpr
        pla3            -- delta reduction
        (λ _ => false)  -- no propositional variables in pla3: placeholder
        i3              -- arithmetic variable interpretation from above

-- predict the answer before you check
#eval evalPLAExpr
        {[10] = [10]}
        (λ _ => false)
        i3

/-!
### What About Model Finding?

Models are *solutions* in the form of assignments of
values to variables, such that the variables with these
values satisfy specified logical/mathematical constraints.

Let's see an example (from z3py tutorial, online). Consider
the following puzzle. Spend exactly 100 dollars and buy exactly
100 animals. Dogs cost 15 dollars, cats cost 1 dollar, and mice
cost 25 cents each. You have to buy at least one of each.
How many of each should you buy?

Analysis: we have three unknown numbers, the number of dogs,
of cats, of mice to buy so that cost comes out exactly right.
These unknows we represent by named variables.
-/


-- numeric variables
def c : DMT1.natArithmetic.syntax.Var := ⟨ 0 ⟩     --# cats
def d : DMT1.natArithmetic.syntax.Var := ⟨ 1 ⟩     --# dogs
def r : DMT1.natArithmetic.syntax.Var := ⟨ 2 ⟩     --# rodents

-- numberic variable expressions
def C := DMT1.natArithmetic.syntax.Expr.var c
def D := DMT1.natArithmetic.syntax.Expr.var d
def R := DMT1.natArithmetic.syntax.Expr.var r

-- individual constraints (rel op expressions in arith lifted to relop exprs in PLA)
def cats_constraint := { C ≥ [1] }
def dogs_constraint := { D ≥ [1] }
def rodents_constraint := { R ≥ [1] }
def total_animals_constraint := { C + D + R = [100] }
def total_cost_constraint := { [100] * C  + [1500] * D + [25] * R = [10000] }

-- we now conjoin the RelOp expressions, in *propositional logic (with arith)* using ∧
def problem_specification :=
    (cats_constraint)  ∧
    dogs_constraint ∧
    rodents_constraint ∧
    total_animals_constraint ∧
    total_cost_constraint

/-!
Ok, this this is really cool. We have not only an absolutely precise,
formal specification of the constraints that define what constitutes
an acceptable solution. But there's more! We also have an evaluator
that can tell us whether this formula is true under specified Boolean
and arithmetic interpretations. Let's guess a solution: C = 5, D = 4,
and R = 12. Does tbis *interpretation* (a.k.a "valuation") satisfy the
constraints?
-/

#eval evalPLAExpr
        problem_specification
        (λ _ => false)
        (λ v => match v with
          | (DMT1.natArithmetic.syntax.Var.mk 0) => 5
          | (DMT1.natArithmetic.syntax.Var.mk 1) => 4
          | (DMT1.natArithmetic.syntax.Var.mk 2) => 12
          | _ => 0
        )

/-!
What we already have is remarkable: both a formal language of
propositional logic with natural number arithmetic as a theory
extension, *and* a semantic evaluator that we can use to *check*
whether any proposed *valuation* (interpretation) is a solution
(model). That's pretty darn cool, but it doesn't get us all the
way to where we want to go.

So where is that? A first stop would be a model finder for our
extended language of PL with arithmetic. A model finder for this
language would find values (if there are any) for both Boolean
and arithmetic variables that would make a given expression true.

The ultimate destination would be a validity checker! This kind
of machine would tell us whether a given proposition/expression
is true under *all* interpretations. But now we have variables
that can take on not just one of two values (true/false) but any
number of values, from zero all the way up.

We no longer have any hope of mechanically checking all possible
solutions (interpretations) to see if any are actual solutions
(models). So now what? We offer two solutions, the first augments
traditional Boolean SAT solvers, model finders, and even validity
checkers with powerful but limited "solvers" for different theories
(here arithmetic). The second entails a profound shift: from what
we can call semantic, or *model-theoretic* notions of validity to
what we will come to know as a *proof-theoretic* notion of what it
takes to show that a given proposition is *valid* (true under *all*
conceivable interpetations).
-/

/-!
## Conclusion

To conclude, we've defined by a syntax and an operational semantics
for propositions in PLA. The operational semantics gives us a way to
derive the Boolean value of *any* PLA proposition under interpretation
functions from propositional and arithmetic variables to domain values.
What we do *not* and will not develop here is a theory of model finding
for propositions in PLA.

The reason is that that could require cabilities for solving complex
algebra problems. As a simple example, consider { X * X - [1] = [0] }.
Model finding now involves quadratic integer programming, with X = 1
as the only model. Clearly the formala is not valid. X = 2: 2 * 2 - 1
does not equal 0, so the proposition is false under this *arithmetic*
interpretation of the *arithmetic* variable, X.

So, maybe other people have developed tools we can use to write formal
propositions in propositional logic with natural number arithmetic and
perhaps other theory extensions that include model finders for these far
more expressive extensions of basic propositional logic?
-/
```
