/- @@@

# Semantics

The idea of semantics in Propositional Logic is simple:
provided that we have a function that maps each variable
expression to a Boolean value, then  every expression in
propositional logic has a Boolean value as its meaning.
We will call such a function a *variable interpretation*.

<!-- toc -->

For literal expressions the mapping to Boolean values is
fixed: the meaning of ⊤ is Boolean *true*, and for ⊥ it
is Boolean *false*. For variable expresssions, given an
additional variable interpretation function, the meaning
of a variable expression is the meaning assigned to it
by a variable interpretation function.

Next, the connectives of propositional logic also have
meanings, which are Boolean functions. For example, the
syntactic symbol ∧ has as its semantic meaning the Boolean
*and* function, often written as &&. The meanings of the
other connectives (operators) of predicate logic are defined
similarly: ∨ means ||, ¬ means !, and so forth.

Finally, expressions built from smaller expressions using
the logical connectives have meanings that are determined
*compositionally*. Given an expression, *e1 op e2* (let's
call it *e*), its meaning is determined by first getting
the Boolean meanings of e1 and e2 and by then applying the
Boolean function that is the designated meaning of *op*.
That's it!
@@@ -/

import DMT1.Lectures.L05_theoryExtensions.syntax
import DMT1.Lectures.L05_theoryExtensions.domain
import DMT1.Lectures.L04_natArithmetic.syntax
import DMT1.Lectures.L04_natArithmetic.semantics

namespace DMT1.Lectures.theoryExtensions.semantics

open theoryExtensions.syntax
open theoryExtensions.semantics

--open natArithmetic.syntax

/- @@@
## Fixed Interpretation of Unary Connectives

The first thing we'll do is define what Boolean operators
we mean by the names of our unary and binary "conenctives".
@@@ -/

-- function takes unary operator and returns *unary* Boolean function
-- (Bool -> Bool) means takes *one* Bool argument and "returns" a Bool

def evalUnOp : UnOp → (Bool → Bool)
| (UnOp.not) => Bool.not


/- @@@
## Fixed Interpretation of Binary Connectives

- takes a binary operator and returns corresponding *binary* Boolean function
- (Bool → Bool → Bool) is the type of function that takes two Bools and returns one
@@@ -/

def evalBinOp : BinOp → (Bool → Bool → Bool)
| BinOp.and => Bool.and
| BinOp.or => Bool.or
| BinOp.imp => domain.imp   -- DMT1.lecture.propLogic.semantics.domain.imp
| BinOp.iff => domain.iff  -- likewise

/- @@@
## Structures: Over Which Expressions Are Evaluated

We now have to evaluate expressions over two-element structures,
providing an interpretation for Boolean-valued variables, and an
interpretation for Nat-valued, i.e., arithmetic, variables.
@@@ -/

structure Interp where
(logical : LogicVar → Bool)
(arithmetic : natArithmetic.semantics.Interp)

open Expr

/- @@@
## Semantic Evaluation
@@@ -/

def eval : Expr → Interp → Bool
| (lit_expr b),             _ => b
| (var_expr v),           i => i.logical v
| (un_op_expr op e),      i => (evalUnOp op) (eval e i)
| (bin_op_expr op e1 e2), i => (evalBinOp op) (eval e1 i) (eval e2 i)
| (arith_pred_expr e),    i => natArithmetic.semantics.evalPredExpr  e i.arithmetic


end DMT1.Lectures.theoryExtensions.semantics
