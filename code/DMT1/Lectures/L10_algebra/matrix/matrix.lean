import Mathlib.Data.Matrix.Defs
import Mathlib.Data.Matrix.Basic

/- @@@
# Matrix M N α

An M × N matrix with entries of type α is represented
as a value of type Matrix m n α. That is then defined
to be the function type M → N → α. Indices thus range
over values of arbitrary types. For finite index sets
we will use Fin typesfor both rows and columns. Matrix
(Fin m) (Fin n) α is thus the type of 2 x 2 matrices,
indexing from [0, 1] in each dimension to α elements.
@@@ -/

open Matrix

/- @@@
Here's an example of a 2 x 2 rational matrix using
standard natural number indexing and notation that
comes with Lean's Matrix types.
@@@ -/
def myMatrix : Matrix (Fin 2) (Fin 2) ℚ :=
  ![![1, 0],
    ![0, 2]]


/- @@@
## Linear Equivalences
Let's now jump stright from α matrices to linear
equivalences. A linear equivalence is a bijective
function between two linear spaces. You can think
of there being a function that maps vectors from
one module to corresponding vectors in the other,
the inverse function. That it's a bijection means
every object goes to a unique object in the other
module and comes right back under *inverse*.

For us, a linear equivalence will be between two
*modules*, where scalarscan lack multiplicative
inverses. So in general there are no fractions or
fractions of actions in modules. To make a module,
which is almost a vector space, into one, give it
multiplicative inverses.
@@@ -/

/- @@@
## Between Modules

We have already established that our *Vc* vectors
form a module, formalized as *Module α (Vc α n)]*:
the type of module with *Vc* objects as the vectors
with α scalars. They also form a vector space with
α being an *field*. As ℚ is a field, we are working
with vector spaces without that being explicit.

So let's think about what a linear equivalence will
look like between *Module α (Vc α n)]* and itself.
A forward function would transform any vector in the
space to a corresponding vector in the same space,
with the inverse function taking that object back
to the start.

On the proverbial left, we have a Module α (Vc α n)]
and another one on the right. In between we'll need
representation of the forward and inverse functions.

The standard computation-oriented representation of
a linear mapping in linear algebra is as a matrix of
scalars. That's what we should use here.

Now we want not just any linear mapping but on that
is bijective, thus also invertible. So in addition
to representing a linear equivalence as a matrix we
can add a a proof that that matrix and thus the map
is invertible.

One way to know is to check whether its determinant
is zero. Another possible design would require that
the client pass two matrices, one the inverse of the
other, with a proof that's true in any instance (you
can again always *sorry* out your proofs as a way to
make progress).
@@@ -/


/- @@@
## TO DO

### A. Define a LinEqSelf type

Building on what we've provided define a *LinEqSelf*
type for representing linear equivalences between a
module and itself. Parameters will probably have to
include the shared scalar type), α, the *vector* type,
for us it's *Vc α n*, and and one or two α matrices
that specify the intended map and its inverse.

### B. Give Some Examples

Instantiate your type with different transformation
matrices. If you can, show examples, in 1, 2, and 3
dimensions. You'll need some kind of function to apply
the map, or its inverse, to a given vector.

### C. Organize as Extension

Organize your work as an extension of the cleaned up
design for affine spaces in Chapter 10. You will add
a linEqSelf directory, with one file linEqSelf.lean).

### D. To submit

Zip and submit your extended version of the codebase
we provided.
@@@ -/

/- @@@
## Extra Credit

- Generalize to maps between different modules then
show, by instantiating your type, that there's a linear
equivalence between *Vc* and *Fin n → α* values under
all the usual operations.
- Define a function or new constructor that allows one
to create a linear equivalence by giving not a matrix
(or two) but an n-tuple of vectors, each intended to be
the image of the corresponding unit vector under the map.
- Pick any element of the problem space to formalize and
automate, do something interesting, and explain briefly
what you did, with a pointer to your code.
@@@ -/
