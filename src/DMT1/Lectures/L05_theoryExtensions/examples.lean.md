```lean
import DMT1.Lectures.L05_theoryExtensions.syntax
import DMT1.Lectures.L05_theoryExtensions.semantics
```

# Examples

<!-- toc -->


```lean
namespace DMT1.Lectures.theoryExtensions.axioms

open theoryExtensions.syntax
open theoryExtensions.semantics
--open natArithmetic.syntax


open Expr
```


## Variable Expressions

```lean
-- Propositional variables expressions
def P : Expr := {⟨0⟩}
def Q : Expr := {⟨1⟩}
def R : Expr := {⟨2⟩}


-- Arithmetic variables
def v₀ : natArithmetic.syntax.Var :=  ⟨0⟩
def v₁ : natArithmetic.syntax.Var := ⟨1⟩
def v₂ : natArithmetic.syntax.Var := ⟨2⟩

-- Arithmetic variable expressions
def K : natArithmetic.syntax.OpExpr :=  natArithmetic.syntax.OpExpr.var v₀
def N : natArithmetic.syntax.OpExpr := natArithmetic.syntax.OpExpr.var v₁
def M : natArithmetic.syntax.OpExpr := natArithmetic.syntax.OpExpr.var v₂

-- Some expressions in "propositional logic with arithmeic"

#check (K + M)

#check (K == M)

-- predicate expression in arithmetic
#check (K == M)

-- predicate expression in propositional logic with arithmetic
def bar := Expr.arith_pred_expr (K == M)


-- and expression (conjunction) in PL with arithmetic
def x := bar ∧ bar


-- a two-interpretation structure

def i : Interp := ⟨ (λ v => true), (λ v => 0)  ⟩

def newI : Interp := ⟨ (λ v => true), (λ v =>
  match v with
  | natArithmetic.syntax.Var.mk 0 => 0    --K
  | natArithmetic.syntax.Var.mk 1 => 1    -- N
  | natArithmetic.syntax.Var.mk 2 => 1
  | _ => 0) ⟩

-- evaluating PL with arithmetic over this structure
#reduce eval x i
#reduce eval x newI

end DMT1.Lectures.theoryExtensions.axioms
```
