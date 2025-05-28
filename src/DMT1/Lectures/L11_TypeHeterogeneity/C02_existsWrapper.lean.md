```lean
import Mathlib.Data.Fin.VecNotation
```



# Existential Wrappers

In this approach we wrap a value of any type α, α itself,
and a typeclass instance or other metadata specialized for
that particular type, α. Because one cannot destructure a
type in Lean, one can't tell what type it is. The type is
known to *exist* but it's effectively hidden (even if one
can access the α field).

```lean
class Typename (α : Type u) where
(toString : String)

instance : Typename Nat := ⟨ "Nat" ⟩
instance : Typename Bool := ⟨ "Bool" ⟩
instance : Typename String := ⟨ "String" ⟩

structure Showable where
  α : Type
  val : α
  valToString : ToString α
  typeToString : Typename α
```


## Existential Hiding

From a client's perspective, one knows that the value of the
α is *some* type, and that the value of the *val* field is of
that type, but the actual type is no longer recoverable. There
is no question that it *exists*, but as one cannot pattern match
on types there is no way to learn what type it is. Information
about the The the value of α and thus the type of *val* is lost.

Here's a demonstration.

```lean
-- Here's a showable instance
def aShowable : Showable := ⟨ Nat, 0, inferInstance, inferInstance ⟩

-- We can access its fields, including the *val* fields
#eval aShowable.val   -- no problem, a simple field access


-- But the value of α and the type of val are unrecoverable
#check aShowable.val  -- all we know is that the type is α
--#eval aShowable.α     -- uncomment to see the error here
```

## Typesafe Operations on Existentially Wrapped Values

The power of existential wrapping comes from the inclusion of
type-specific class instances with wrapped types and their values.
The *aShowable* object, for example, carries typeclass instances
as field values in turn carry type-specific metadata for α which
can include operations. Here they are used to obtain type-specific
string values for both α and *val*.

```lean
-- Showables with three distinct underlying types
def natShowable : Showable := ⟨ Nat, 3, inferInstance, inferInstance ⟩
def boolShowable : Showable := ⟨ Bool, true, inferInstance, inferInstance ⟩
def stringShowable : Showable := ⟨ String, "I love maths", inferInstance, inferInstance ⟩

-- We can obtain String names for the underlying types
#eval natShowable.typeToString.toString
#eval boolShowable.typeToString.toString
#eval stringShowable.typeToString.toString

-- We can obtain String renditions of the underlying values
#eval natShowable.valToString.toString natShowable.val
#eval boolShowable.valToString.toString boolShowable.val
#eval stringShowable.valToString.toString stringShowable.val

-- A function returning "(val : type)" for a showable
def toTypedValString (s : Showable) :=
  let valName := s.valToString.toString s.val
  let typeName := s.typeToString.toString
  "(" ++ valName ++ " : " ++ typeName ++ ")"

-- A list of Showables with heterogeneous underlying types
def showables := [ natShowable,  boolShowable, stringShowable ]

-- And the punch line: we can "show" an output for each of them
#eval List.map toTypedValString showables
```

## Signature: N-tuple of Showables

We model a signature as a function from position/index
to Showable.

```lean
def Sig (n : Nat) := Fin n → Showable

-- Convert a signature to a string
def showSig {n : Nat} (sig : Sig n) : String :=
  "[" ++ String.intercalate ", " (List.ofFn (fun i => toTypedValString (sig i))) ++ "]"

-- Example Sig
def aSig : Sig 3 := ![natShowable, boolShowable, stringShowable]

-- Convert to String
#eval showSig aSig
-- Output: "[Nat : 42, Bool : true, String : hello]"
```

## Modeling Modules

From here, we represent a module as a tuple of signatures.

TODO.


## Discussion

This approach to heterogeneity is extensible. To add support for any type
one need only have the required typeclass instances. The approach is also
type-safe. There is an added runtime cost insofar as instances are passed
and used at runtime, preventing inlining and incurring the costs of making
indirect function calls.
