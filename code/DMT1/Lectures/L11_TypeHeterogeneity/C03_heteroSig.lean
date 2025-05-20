/- @@@
# Finite-Index Signature Tuples (Fin n → σ i)

 dependently-typed, index-based tuple representation, good for
 repreesenting fixed-arity, heterogeneously-typed structures.
@@@ -/

namespace DMT1.Lecture.hetero.hetero

open Std

-- A heterogeneous n-tuple type: σ is a signature Fin n → Type
def Sig (n : Nat) := Fin n → Type
def Val (σ : Sig n) := ∀ i : Fin n, σ i

-- Collects Repr instances for a given signature
class BuildReprs {n : Nat} (σ : Sig n) where
  reprs : ∀ i : Fin n, Repr (σ i)

-- Pretty print each entry using its Repr instance
def toReprList {n : Nat} {σ : Sig n} [BuildReprs σ] (v : Val σ) : List String :=
  List.ofFn (fun i => Format.pretty ((BuildReprs.reprs i).reprPrec (v i) 0) 80)

def toPrettyString {n : Nat} {σ : Sig n} [BuildReprs σ] (v : Val σ) : String :=
  s!"[{String.intercalate ", " (toReprList v)}]"

-- Example signature and value
def sig3 : Sig 3
| 0 => Nat
| 1 => Bool
| 2 => String

def val3 : Val sig3
| 0 => (42 : Nat)
| 1 => true
| 2 => "hello"

instance : BuildReprs sig3 where
  reprs
  | 0 => inferInstanceAs (Repr Nat)
  | 1 => inferInstanceAs (Repr Bool)
  | 2 => inferInstanceAs (Repr String)


#eval toPrettyString val3 -- "[42, true, hello]"



/- @@@
- Fixed-length, statically typed heterogeneity
- statically typed, fixed arity tuples with per-index types
- Fast index-based access (like arrays)
- Dependent functions on each component

- Suitable for modeling e.g. function signatures and argument packs, struct layouts, schemas

Compared to HList, this gives you:
- Random access via Fin n rather than recursive pattern matching
- Better performance and inference in many cases?
- More natural fit for modeling arities of known size?
@@@ -/


end DMT1.Lecture.hetero.hetero
