/- @@@
# Truth Tables

<!-- toc -->


Given expression, *e*, a truth table for *e* is a list
of all 2^n interpretations for *e* with each one paired
with the value of *e* under it. The primary function that
this module defines takes an expression and returns the
list of its output values under each interpretation for
that expressiom. From this information a truth table can
be assembed.
@@@ -/

import DMT1.Lectures.L02_propLogic.formal.interpretation

namespace DMT1.Lectures.propLogic.semantics.models
open propLogic.syntax

/- @@@
Compute and return the list of Bool values
obtained by evaluating an expression, *e*, under
each interpretation, *i*, in a given list of them.
@@@ -/
def mapEvalExprInterps : Expr → List Interp → List Bool
| _, [] => []
| e, h::t => (⟦e⟧h)::mapEvalExprInterps e t

/- @@@
Return the list of Bool values obtaibed by evaluating
an expression, e, over each of its interpretations, in
their natural order.
@@@ -/
def mapEvalExprAllInterps : Expr → List Bool
| e =>  mapEvalExprInterps e (interpsFromExpr e)

-- just another name for this function
def truthTableOutputs := mapEvalExprAllInterps

end DMT1.Lectures.propLogic.semantics.models
