import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Lean.Data.Json

open Fin Lean Json

/- @@@
# Custom Dyn Types

Define an inductive type with cases for each
supported data or function type.
@@@ -/

/- @@@
Wrapper for type-tagged values of heterogeneous types
@@@ -/
inductive DynVal where
  | nat  : Nat → DynVal
  | str  : String → DynVal
  | bool : Bool → DynVal
  | natToBool  : (Nat → Bool) → DynVal
  | natToNat   : (Nat → Nat) → DynVal
  | strToBool  : (String → Bool) → DynVal
  | boolToStr  : (Bool → String) → DynVal


/- @@@
## Pattern Matching on (Destructuring) Psuedotypes
Having mapped each supported type to a corresponding
constructor, we can now effectively match on types by
matching on their associated DynVal constructors (we'll
call these *pseudotypes*). Here, given a wrapped value,
we match on its pseudotype to extract the wrapped value,
from which we, in this case, derive a printable version
of that value.
@@@ -/
def dynValToString : DynVal → String
  |DynVal.nat n        => toString n
  |DynVal.str s        => s
  |DynVal.bool b       => toString b
  |DynVal.natToBool _  => "<Nat → Bool>"
  |DynVal.natToNat _   => "<Nat → Nat>"
  |DynVal.strToBool _  => "<String → Bool>"
  |DynVal.boolToStr _  => "<Bool → String>"

/- @@@
## Typeclass Instances for Printing of Wrapped Values
@@@ -/
instance : Repr DynVal where reprPrec m _ := dynValToString m
instance : ToString DynVal := { toString := dynValToString }

/- @@@
## Dynamic Type Tags

Just as we associate a pseudo-typed value DynValye constructor
with each supported type, so we associate a DynType type tag with
each such type. We can pass these tags as data, define functions
to associated metadata, such as printable type names, etc.
@@@ -/

inductive DynType where
  | nat
  | str
  | bool
  | fn (dom cod : DynType)


/- @@@
## Printable Type Names
@@@ -/
def dynTypeToString : DynType → String
  | .nat        => "Nat"
  | .str        => "String"
  | .bool       => "Bool"
  | .fn d c     => s!"({dynTypeToString d} → {dynTypeToString c})"


/- @@@
## Signature: n-tuple of DynTypes

We model a signature as a function from position/index
to DynType. These are the type tag,s not wrapped values.
@@@ -/
def Sig (n : Nat) := Fin n → DynType


-- Example: (Nat, Bool)
def aSig1 : Sig 2 := fun (i : Fin 2) => match i with
| 0 => .nat
| 1 => .str

def aSig2 (_ : String) : (Sig 3) :=
  fun
  | 0 => .nat
  | 1 => .str
  | 2 => .bool


/- @@@
## Valuation of a Signature

We define *Args* to the *type* of a tuple of actual
values matching the types in a given Sig (itself a tuple
of type tags). We can call such a value type  a *valuation*
of a signature.
@@@ -/
def Args {n : ℕ} (s : Sig n) : Type :=
  ∀ i : Fin n, match s i with
    | .nat => Nat
    | .str => String
    | .bool => Bool
    | .fn _ _ => String -- TODO

-- Example
def args1 : Args aSig1 := fun (i : Fin 2) => match i with
| 0 => (3 : Nat)
| 1 => "Hello"

#eval args1 0
#eval args1 1



/- @@@
Example of pseudotype-checked arg tuple
@@@ -/
def args2 : Args (aSig2 "String")
| 0 => (42 : Nat)
| 1 => "Lean 4"
| 2 => true

/- @@@
##
A function taking a valuation of a signature and returning
a tuple of heterogeneously typed dynamic values (DynVal).
@@@ -/
def wrapArgs {n : ℕ} (s : Sig n) (args : Args s) : Fin n → DynVal :=
  fun i =>
    match s i, args i with
    | .nat,       x => .nat x
    | .str,       x => .str x
    | .bool,      x => .bool x
    | .fn _ _,    x => .str x



/- @@@
## Apply Dynamic Function to Dynamic Argument

Dynamically checked application of a wrapped function, f,
to a dynamically checked, wrapped argument, x. Returns Option
result.
@@@ -/
def applyIfTyped : DynType → DynVal → DynVal → Option DynVal
  | .fn .nat .bool, DynVal.natToBool f, DynVal.nat x => some (DynVal.bool (f x))
  | .fn .nat .nat, DynVal.natToNat f, DynVal.nat x => some (DynVal.nat (f x))
  | .fn .str .bool, DynVal.strToBool f, DynVal.str x => some (DynVal.bool (f x))
  | .fn .bool .str, DynVal.boolToStr f, DynVal.bool x => some (DynVal.str (f x))
  | _, _, _ => none

-- Example
#eval
applyIfTyped                                -- expect *false*
  (.fn .nat .bool)                          -- know the function type
  (DynVal.natToBool (fun n => n%2 == 0))    -- wrap one of that type
  (DynVal.nat 3)                            -- and apply to wrapped value

/- @@@
## Example: A Signature with Named Fields and a Valuation

In this extended example, we build a structure that comprises
a signature, a valuation, field names, all for an existential
number, *n*, of fields. We start by defining what an entry for
one value will comprise in such a structure; then we define the
structure itself.
@@@ -/

/- @@@
### Entry
@@@ -/

structure ModEntry where
  {n : ℕ}
  names : Fin n → String
  sig   : Sig n
  args  : Args sig

-- A convenience function (TODO: take out args part)
def mkModEntry {n : ℕ} (names : Fin n → String) (sig : Sig n) (args : Args sig) : ModEntry :=
  { names := names, sig := sig, args := args }

-- Printing helper functions
def printModEntry (e : ModEntry) : List (String × String) :=
  let dynArgs := wrapArgs e.sig e.args
  List.ofFn fun i => (e.names i, dynValToString (dynArgs i))

def printSigEntry (e : ModEntry) : List (String × String) :=
  List.ofFn fun i => (e.names i, dynTypeToString (e.sig i))

def getFieldNames (e : ModEntry) : List String :=
  List.ofFn fun i => e.names i

-- Return (name, type, value) triples from a ModEntry
def printTypedModEntry (e : ModEntry) : List (String × String × String) :=
  let dynArgs := wrapArgs e.sig e.args
  List.ofFn fun i => (e.names i, dynTypeToString (e.sig i), dynValToString (dynArgs i))

-- Return (name, type) pairs from a ModEntry
def printFieldSigEntry (e : ModEntry) : List (String × String) :=
  List.ofFn fun i => (e.names i, dynTypeToString (e.sig i))


/- @@@
## Downcasting: Accessing Wrapped Values

This design method loses type information in the sense that once
a value is wrapped, one can no longer determine what type of value
is in there, except by pattern matching on pseudotype tags, yielding
Option-valued results.

Here's an example where we are given a ModEntry that we expect to
contain a function of some kind. We pattern match and fail if that is
not the case. Otherwise we wrap the arguments carried by the ModEntry
and apply the wrapped function to it. If that succeeds we get a wrapped
result, otherwise *from applyIfTyped* we would also get an option *None.*
@@@ -/
def evalModEntryField (e : ModEntry) (i : Fin e.n) (fnVal : DynVal) : Option DynVal :=
  match e.sig i with
  | .fn dom cod =>
    let argVal := wrapArgs e.sig e.args i
    applyIfTyped (.fn dom cod) fnVal argVal
  | _ => none

/- @@@
## Module (A Tuple of Entries)

Now we define a *Module* as just an n-tuple of ModEntry's,
each comprising an existential *n*, a tuple of field names,
a signature (tuple of field type tages), and a valuation (a
tuple of values of the types associated with those type tags),
@@@ -/

structure Module (n : ℕ) where
  entries : Fin n → ModEntry

-- Printing as string functions
def printModuleEntries {n : ℕ} (m : Module n) : List (List (String × String)) :=
  List.ofFn fun i => printModEntry (m.entries i)

def printModuleSigs {n : ℕ} (m : Module n) : List (List (String × String)) :=
  List.ofFn fun i => printSigEntry (m.entries i)

def printTypedModule {n : ℕ} (m : Module n) : List (List (String × String × String)) :=
  List.ofFn fun i => printTypedModEntry (m.entries i)

def printFieldSigModule {n : ℕ} (m : Module n) : List (List (String × String)) :=
  List.ofFn fun i => printFieldSigEntry (m.entries i)

-- Printing as JSON functions
def jsonFromPairs (pairs : List (String × String)) : Json :=
  Json.mkObj (pairs.map fun (k, v) => (k, Json.str v))

def modEntryValuesJson (e : ModEntry) : Json :=
  jsonFromPairs (printModEntry e)

def modEntryTypesJson (e : ModEntry) : Json :=
  jsonFromPairs (printSigEntry e)

def moduleValuesJson {n : ℕ} (m : Module n) : Json :=
  Json.arr <| Array.ofFn fun i => modEntryValuesJson (m.entries i)

def moduleTypesJson {n : ℕ} (m : Module n) : Json :=
  Json.arr <| Array.ofFn fun i => modEntryTypesJson (m.entries i)

def moduleValuesJsonString {n : ℕ} (m : Module n) : String :=
  (moduleValuesJson m).pretty

def moduleTypesJsonString {n : ℕ} (m : Module n) : String :=
  (moduleTypesJson m).pretty

/- @@@
## Example usage
@@@ -/

def names2 : Fin 3 → String
| 0 => "id"
| 1 => "desc"
| 2 => "flag"


/- @@@
A module entry (like a simplistic method specification in a class)
@@@ -/
def entry1 : ModEntry := mkModEntry names2 (aSig2 "String") args2

/- @@@
Example signature, sig 2, with one field of pseudo-type Nat
@@@ -/
def sig3 : Sig 1
| 0 => .nat

-- A corresponding argument 1-tuple, (41)
def args3 : Args sig3
| 0 => (41 : Nat)

-- A cooresponding 1-tuple of field names
def names3 : Fin 1 → String
| 0 => "count"

-- a second module entry
def entry2 : ModEntry := mkModEntry names3 sig3 args3

-- Module with 2 entries
def mod1 : Module 2 where
  entries
    | 0 => entry1
    | 1 => entry2

/- @@@
An example with a function-valued entry
@@@ -/
def sig4 : Sig 1
| 0 => .fn .str .bool

def args4 : Args sig4
| 0 => "nonempty?"

def names4 : Fin 1 → String
| 0 => "check"

def entry4 : ModEntry := mkModEntry names4 sig4 args4

def fnEntry4 : DynVal := DynVal.strToBool (fun (s : String) => s ≠ "")

instance : Repr (Option DynVal) where
  reprPrec o _ :=
    match o with
    | Option.none => "None"
    | Option.some m => s!"Some {m})"

#eval applyIfTyped (.fn .str .bool) fnEntry4 (DynVal.str "hello")   -- Expected: some (dynVal.bool true)
#eval applyIfTyped (.fn .str .bool) fnEntry4 (DynVal.str "")        -- Expected: some (dynVal.bool false)


/- @@@
Ok, now let's test typed application of pseudotyped partial functions
to pseudotyped arguments, possibly returning Option.none.
@@@ -/
def fnEntry3 : DynVal :=DynVal.natToBool (fun (n : Nat) => n % 2 == 0)

#eval evalModEntryField entry2 (0 : Fin 1) fnEntry3  -- Expected: some (dynVal.bool false)
#eval evalModEntryField entry4 (0 : Fin 1) fnEntry4  -- Expected: some (dynVal.bool true)


-- JSON printing of module entries
#eval moduleTypesJsonString mod1
#eval moduleValuesJsonString mod1
#eval modEntryTypesJson entry1
#eval modEntryValuesJson entry1
#eval printModuleEntries mod1


namespace DMT1.Lecture.hetero.hetero

/- @@@
## Discussion

- Store heterogeneous values in (List MyDyn).
- Loses static type information
- Must either downcast to use or package instances with values
- Useful with JSON-style serialization
- Dynamic modules or configurations
- Interfacing with external systems
@@@ -/

end DMT1.Lecture.hetero.hetero
