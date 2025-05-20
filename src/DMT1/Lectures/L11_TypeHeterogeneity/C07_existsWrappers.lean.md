# Existential Wrappers

In this approach we wrap a value of any type α, α itself,
and a typeclass instance or other metadata specialized for
that particular type, α. Because one cannot destructure a
type in Lean, one can't tell what type it is. The type is
known to *exist* but it's effectively hidden (even if one
can access the α field).

```lean
structure Showable where
  α : Type
  val : α
  inst : ToString α

def natShow : Showable := ⟨ Nat, 3, inferInstance ⟩

#eval natShow.inst.toString natShow.val
```

## Existential Hiding
From a client's perspective, one knows that the contained
value has a type, that that type *exists*, but not what it
is exactly. One also knows that the contained instance is
valid for whatever that type is and so can hold functions
and data applicable to it. The power of this approach comes
from its abstracting from the underlying type hetergeneity
while still providing means to operate on each value in a
type-specific manner.


## Exanple
With that, as an example we can maintain a List of
uniformly-typed Showables hiding heterogeneously typed
values along with applicable instance-provided metadata
and operations.


## Discussion

This approach to heterogeneity is extensible. To add support for any type
one need only have the required typeclass instances. The approach is also
type-safe. There is an added runtime cost insofar as instances are passed
and used at runtime, preventing inlining and incurring indirection costs.
