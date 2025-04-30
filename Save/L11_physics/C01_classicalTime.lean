-- import DMT1.Lectures.L09_classes.C06_finiteDimensional
import Mathlib.LinearAlgebra.Basis.Defs

/- @@@
# Affine Time

We can intuit time as unfolding in a linear fashion,
but there's even less to it than that. For linearity
assumes a distinguished origin, while in classical
reality, there really isn't one, just as there is no
distinuished origin of the plane (approximately) on
which you're supported. Removing that idea let's you
better see what classical time is: it's very space,
a set of undistinguished and indistinguishable points,
isomorphic, but not comparable to, the space of n-dim
scalar tuples.

Vectors, represented in the same way, arise as
directed differences between points. If a vector, v,
is viewed as an action, then v operates on a point,
p1, leading to the point, at the pointed end of the
vector, to p2. That vector, added to p1, goes right
back to p2. It has to work so (p2 - p1) +ᵥ p1 = p2.
The vector space elements are *differences* between
points.

Vectors are relative. Points absolute; but also
anonymous and indistinguisable. At least vector spaces
have distinguished origins. Vectors are derivative of
points, thus lossy. Let not thy vision be limited to
vector concepts. You are pointed onto a better path.

## Classical Time

We'll formally represent classical time as a ℚ affine
1-space. It's a coordinate free line of points in time
without beginning or end. Vectors, diffenences between
points, are directed durations.

To make such an abstraction useful will sometimes
require coordinates. Coordinates are n-dimensional
α tuples that correspond to the points. Crucially,
coordiantes enable computation, but there are other
purposes as well.

So now think of a torsor of points, all alike. Pick
a point, any point, it doesn't mapper. In practice,
what does often matter deeply, is the attachement of
a physical or human interpretation to that point.

For example, we could say, let *o* be an arbitrary
point that henceforce we'll inerpret as representing
The earliest moment of all on January 1, 1970.

In addition to that point in time, we can represent
any other point as some scalar multiple of some fixed,
non-zero *basis* vector, added to that *origin* point.

Just as the choice of an origin calls for a real world
interpretation of it, so it is with the interpretation
of that basis vector. The physical meaning in the case
of time is that it's a non-zero vector representing a
*duration* of 1 millisecond (itself referenced to some
interpretation). Now every point has its coordinates,
(just one) expressed as the *ordered tuple of scalars
you need to multiply the (ordered) basis vectors by to
get a vector that takes the origin to the target point.

## Affine Coordinate Spaces

It's notable that the set of sll coordinate tuples
needed to map onto all of the points of a rational
n-dimensional torsor will itself have the structure
of an affine space: an affine coordinate space. The
points, again, are now *coordinate tuples* as are the
vectors, determined by the choice of affine frame.

To have an affine frame, we need a point and a set
of basis vectors for the vector space. But where do
we get a first point and such basis vectors from, so
as to get started, e.g., representing other points?

As all points in a torsor are indistinguishable, just
pick one arbitrarily and commit to interpreting, and
treating,it as an origin. Any point will do. To make
it simple, we'll use (0 : Point α n). We might call it
the *standard origin*. We will leave documentation of
the intended interpretation to downstream clients of
this API.

[link](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Basis/Defs.html#Basis)

For computational purposes, it works to represent the
basis as an a tuple of basis vectors, satsifying the
basis axioms. We will

Focus on
that scalar multiplier. *That* is the coordinate (1-d
here but easily generalized) of the point with respect
to the frame of reference formed by the combination of
the origin point and given set of basis vectors (here
just one) superimposes a coordinate system on the whole
space.
for
(as long as we have some non-zero vecto to start with).


(coordinate addresses, as it were), to points.

poimts is to pick
an arbitrary point (because they're all the same) as
an origin, and basis vectors spanning the space, and
voila, every other point is the origin plus or minus
any other vector whatsoever.


A coordinate free set of points. Just that is a lot.
They could be points in any dimensional space, but
just as classical time is featureless in extending
to infinity in each direction, There's no coordinate
system nativelyy on the 2-d plane of the floor. We do
use concrete representations. They are not conceptually
necessary but they do have to satisfy all of the axioms.
@@@ -/

structure Time where


/- @@@
The same vector, v, can act to displace any point,
and the axioms ensure that the algebra stays clean
and intuitive. For example, no matter what kinds of
things are being combined, if they follow the axioms
then you can operate with them using our new algebra.
And it can be computable, too.
@@@ -/
