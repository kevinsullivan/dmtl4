/- @@@
# Custom Dyn Types

Define an inductive type with cases for each
supported data or function type.
@@@ -/

namespace DMT1.Lecture.hetero.hetero

inductive MyDyn where
  | nat : Nat → MyDyn
  | str : String → MyDyn
  | bool : Bool → MyDyn

/- @@@
- Store heterogeneous values in (List MyDyn).
- Useful with JSON-style serialization [or dynamic programming]
- Loses static type information.
- Must downcast to use values — potentially unsafe unless carefully checked.
- Dynamic modules or configurations.
- Interfacing with external data or plugin systems.
@@@ -/

end DMT1.Lecture.hetero.hetero
