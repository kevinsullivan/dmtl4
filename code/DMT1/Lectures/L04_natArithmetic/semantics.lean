import DMT1.Lectures.L04_natArithmetic.syntax
import DMT1.Lectures.L04_natArithmetic.domain

namespace DMT1.Lectures.L04_natArithmetic.semantics
open DMT1.Lectures.L04_natArithmetic.domain

/- @@@
Given syntactic operator and predicate terms, return
their fixed semantic meanings as Nat- and Bool-valued
functions.
@@@ -/
open DMT1.Lectures.L04_natArithmetic.domain
open DMT1.Lectures.L04_natArithmetic.syntax

def evalUnOp : UnOp → (Nat → Nat)
| UnOp.inc    => Nat.succ
| UnOp.dec    => Nat.pred
| UnOp.fac    => domain.fac

def evalBinOp : BinOp → (Nat → Nat → Nat)
| BinOp.add => domain.add
| BinOp.sub => domain.sub
| BinOp.mul => domain.mul

def evalBinPred : BinPredOp → (Nat → Nat → Bool)
| BinPredOp.eq => domain.eq    -- eq is from from natArithmetic.domain
| BinPredOp.le => domain.le    -- etc.
| BinPredOp.lt => domain.lt
| BinPredOp.ge => domain.ge
| BinPredOp.gt => domain.gt

def evalUnPred : UnPredOp → (Nat → Bool)
| UnPredOp.isZero => domain.isZero

/- @@@
A helper function for evaluating "literal n"
expressions, to simplify the expression of
the semantic evaluation function defined
below.
@@@ -/
def evalLit (n : Nat) : Nat := n

/- @@@
A more abstract name for the *type* of a
variable interpretation.
@@@ -/
def Interp := Var → Nat

/- @@@
A helper function for evaluating variables
under given interpretations.
@@@ -/
def evalVar : Var → Interp → Nat  -- evalVar is a function
| v, i => i v   -- apply interpretation i to variable v to get value

/- @@@
@@@ -/
-- Semantic evaluation of arithmetic expression, yielding its Nat value
def eval : ArithExpr → Interp → Nat
| ArithExpr.lit n,          _   => (evalLit n)
| ArithExpr.var v,          i   => (evalVar v i)
| ArithExpr.unOp op e,      i   => (evalUnOp op) (eval e i)
| ArithExpr.binOp op e1 e2, i   => (evalBinOp op) (eval e1 i) (eval e2 i)

/- @@@
Semantic evaluation of a predicate expression.
@@@ -/
--
def evalPredExpr : PredExpr → Interp → Bool
| PredExpr.unOp op e, i =>  (evalUnPred op) (eval e i)
| PredExpr.binOp op e1 e2, i =>  (evalBinPred op) (eval e1 i) (eval e2 i)

/- @@@
Standard concrete notation for applying semantic
evaluation functions to expressions.
@@@ -/
notation "⟦" e "⟧"  => eval e
notation "⟦" e "⟧" => evalBinPred e

end  DMT1.Lectures.L04_natArithmetic.semantics
