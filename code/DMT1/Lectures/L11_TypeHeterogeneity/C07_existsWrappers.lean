/- @@@
# Existential Wrappers

wrap a value along with a typeclass instance or other metadata
structures, hiding its exact type behind an existential. Here 's
a standard example.
@@@ -/

structure Showable where
  α : Type
  val : α
  inst : ToString α

/- @@@
With that, as an example we can maintain a List of
uniformly-typed Showables hiding heterogeneously typed
values along with applicable instance-provided metadata
and operations.
@@@ -/
