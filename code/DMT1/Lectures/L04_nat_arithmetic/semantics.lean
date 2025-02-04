import DMT1.Lectures.L04_nat_arithmetic.syntax
import DMT1.Lectures.L04_nat_arithmetic.domain

namespace DMT1.Lectures.L04_nat_arithmetic.semantics
open DMT1.Lectures.L04_nat_arithmetic.domain

/- @@@
@@@ -/
-- given syntactic operator terms, return corresponding Nat- and Bool-valued functions
open DMT1.Lectures.L04_nat_arithmetic.domain
open DMT1.Lectures.L04_nat_arithmetic.syntax

def evalUnOp : UnOp → (Nat → Nat)
| UnOp.inc    => Nat.succ
| UnOp.dec    => Nat.pred
| UnOp.fac    => domain.fac
--| UnOp.doub   => (fun n => n * 2)
--| UnOp.halve  => (fun n => n / 2)

def evalBinOp : BinOp → (Nat → Nat → Nat)
| BinOp.add => domain.add
| BinOp.sub => domain.sub
| BinOp.mul => domain.mul

def evalBinPredOp : BinPredOp → (Nat → Nat → Bool)
| BinPredOp.eq => domain.eq    -- eq is from from natArithmetic.domain
| BinPredOp.le => domain.le    -- etc.
| BinPredOp.lt => domain.lt
| BinPredOp.ge => domain.ge
| BinPredOp.gt => domain.gt

def evalUnPredOp : UnPredOp → (Nat → Bool)
| UnPredOp.isZero => domain.isZero

/- @@@
@@@ -/
-- a function for evaluating "literal n" expressions -- it's just n
def evalLit (n : Nat) : Nat := n

/- @@@
@@@ -/
-- The *type* of an interpretation
def Interp := Var → Nat

/- @@@
@@@ -/
-- A function for evaluating variable values under given interpretations
def evalVar : Var → Interp → Nat  -- evalVar is a function
| v, i => i v   -- apply interpretation i to variable v to get value

/- @@@
@@@ -/
-- Semantic evaluation of arithmetic expression, yielding its Nat value
def eval : Expr → Interp → Nat
| Expr.lit n,          _   => (evalLit n)
| Expr.var v,          i   => (evalVar v i)
| Expr.unOp op e,      i   => (evalUnOp op) (eval e i)
| Expr.binOp op e1 e2, i   => (evalBinOp op) (eval e1 i) (eval e2 i)

/- @@@
@@@ -/
-- Semantic evaluation of a relational expression, with a Boolean indication
def evalPredExpr : PredExpr → Interp → Bool
| PredExpr.unOp op e, i =>  (evalUnPredOp op) (eval e i)
| PredExpr.binOp op e1 e2, i =>  (evalBinPredOp op) (eval e1 i) (eval e2 i)

/- @@@
@@@ -/
notation "⟦" e "⟧" i => (eval e i)
notation "⟦" e "⟧" i => (evalBinPredOp e i)

end  DMT1.Lectures.L04_nat_arithmetic.semantics
