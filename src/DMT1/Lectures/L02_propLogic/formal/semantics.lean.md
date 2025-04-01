
<!-- toc -->

# Semantics

The idea of semantics in Propositional Logic is simple:
provided that we have a function that maps each variable
expression to a Boolean value, then  every expression in
propositional logic has a Boolean value as its meaning.
We will call such a function a *variable interpretation*.

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

```lean
import DMT1.Lectures.L02_propLogic.formal.syntax
import DMT1.Lectures.L02_propLogic.formal.domain

namespace DMT1.Lectures.propLogic.semantics

open propLogic.syntax
```



## Fixed Interpretation of Unary Connectives

The first thing we'll do is define what Boolean operators
we mean by the names of our unary and binary "conenctives".

```lean
-- function takes unary operator and returns *unary* Boolean function
-- (Bool -> Bool) means takes *one* Bool argument and "returns" a Bool

def evalUnOp : UnOp → (Bool → Bool)
| (UnOp.not) => Bool.not
```


## Fixed Interpretation of Binary Connectives

- takes a binary operator and returns corresponding *binary* Boolean function
- (Bool → Bool → Bool) is the type of function that takes two Bools and returns one

```lean
def evalBinOp : BinOp → (Bool → Bool → Bool)
| BinOp.and => Bool.and
| BinOp.or => Bool.or
| BinOp.imp => domain.imp   -- DMT1.lecture.propLogic.semantics.domain.imp
| BinOp.iff => domain.iff  -- likewise
```

## Interpretations: Variable Semantics of Variable Expressions
We've now understood that an "interpretation" can be understood
to be and can at least here actually be *used* as a function that
takes a variable (var) as an argument and that returns the Boolean
value that that interpretation assigns to it.

To understand the next line, understand that (var → Bool) in Lean
is the type of any function that takes a var argument and returns a
Bool value. Here we just give this *type* a name to make subsequent
code just a easier for people to read and understand.

```lean
abbrev Interp := Var → Bool

open Expr
```

## Evaluation: Operational Semantics of Predicate Logic

NB: This is the material you most need and want to grok.

Finally now here is the central definition: the semantics of
propositional logic, specified in terms of our representations
of interpretations, variables, etc.

The first line defines evalBoolExpr to be some function taking
an expression, e, and an interpretation, i, as arguments and
returning the Boolean meaining of e in the "world" (binding
of all variables to Boolean values) expressed by that i.

```lean
def eval : Expr → Interp → Bool
| lit_expr b,             _ => b
| (var_expr v),           i => i v
| (un_op_expr op e),      i => (evalUnOp op) (eval e i)
| (bin_op_expr op e1 e2), i => (evalBinOp op) (eval e1 i) (eval e2 i)
```


## Standard Notation for Semantic Evaluation Operator

The standard notation for (eval e i) is ⟦e⟧ᵢ, where ⟦⬝⟧
is notation for the semantic evaluation function, eval.
In Lean we'll write ⟦e⟧i, without *i* being a subscript.

```lean
notation "⟦" e "⟧" i => (eval e i)
#check (e : Expr) → (i : Interp) → ⟦e⟧i
```

That's it. From this material you should be able to aquire
a justifiably confident grasp of essentially every aspect
of the syntax and semantics of propositional logic.

```lean
end DMT1.Lectures.propLogic.semantics
```
