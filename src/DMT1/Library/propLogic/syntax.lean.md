# Syntax

```lean
namespace DMT1.Library.propLogic.syntax

structure Var : Type where
  mk :: (index: Nat)
deriving Repr

inductive UnOp : Type
| not : UnOp
deriving Repr

inductive BinOp : Type
| and
| or
| imp
| iff
deriving Repr

inductive Expr : Type
| lit_expr (from_bool : Bool) : Expr
| var_expr (from_var : Var)
| un_op_expr (op : UnOp) (e : Expr)
| bin_op_expr (op : BinOp) (e1 e2 : Expr)
deriving Repr

open Expr

notation:max " ⊤ " => (Expr.lit_expr true)
notation:max " ⊥ " => (lit_expr false)
notation:max "{" v "}" => (var_expr v)
notation:max "¬" p:40 => un_op_expr UnOp.not p
infixr:35 " ∧ "  =>  Expr.bin_op_expr BinOp.and
infixr:30 " ∨  "  => Expr.bin_op_expr BinOp.or
infixr:20 " ↔ " => bin_op_expr BinOp.iff
infixr:25 " ⇒ " => bin_op_expr BinOp.imp

end DMT1.Library.propLogic.syntax
```
