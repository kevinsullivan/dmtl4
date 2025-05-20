namespace DMT1.Lecture.hetero.hetero

/- @@@
# Heterogeneous Lists (HList)

A heterogeneous list is a list built from nil and cons
constructors wbut where each value in the list is of a type
specified an an element in a corresponding list of types.

<!-- toc -->
@@@ -/

inductive HList : List (Type u) → Type (u+1) where
  | nil : HList []
  | cons {a : Type u} {as : List (Type u)} : a → HList as → HList (a :: as)

namespace HList


/- @@@
## Head and Tail
@@@ -/

/-- Head of an HList -/
def head {α : Type u} {as : List (Type u)} : HList (α :: as) → α
  | cons x _ => x

/-- Tail of an HList -/
def tail {α : Type u} {as : List (Type u)} : HList (α :: as) → HList as
  | cons _ xs => xs

/--
## Utility: Build HLists of Function Types

Give two lists of types, return the list of function types
derived by pairing corresponding entries.
-/
def ZipWithFun : List (Type u) → List (Type u) → List (Type u)
  | [], [] => []
  | a :: as, b :: bs => (a → b) :: ZipWithFun as bs
  | _, _ => []

/- @@@
## Map Hlist of Functions over HList of Arguments
Map an HList of functions over an HList of values
- HList.map b.fs b.xs maps each function in b.fs over the corresponding value in b.xs
- b.fs : HList (ZipWithFun as bs) is a heterogeneous list of functions, each fᵢ of type aᵢ → bᵢ
- b.xs : HList as is a heterogeneous list of values, where each value xᵢ has type aᵢ
-/
def map
  : ∀ {as bs : List (Type u)},
    HList (ZipWithFun as bs) →
    HList as →
    Option (HList bs)
  | [], [], nil, nil => some nil
  | a :: as, b :: bs, cons f fs, cons x xs =>
      match map fs xs with
      | some tail => some (cons (f x) tail)
      | none => none
  | _, _, _, _ => none


/-!
## Pretty-Printing
-/

inductive MapRepr : List (Type u) → Type (u+1)
  | nil  : MapRepr []
  | cons {a : Type u} {as : List (Type u)} (head : Repr a) (tail : MapRepr as) : MapRepr (a :: as)

def toReprList : ∀ {ts : List (Type u)}, HList ts → MapRepr ts → List String
  | [], HList.nil, MapRepr.nil => []
  | a :: as, HList.cons x xs, MapRepr.cons head insts =>
      let str := Std.Format.pretty (head.reprPrec x 0) 80
      str :: toReprList xs insts

def toPrettyString {ts : List (Type u)} (xs : HList ts) (insts : MapRepr ts) : String :=
  s!"[{String.intercalate ", " (toReprList xs insts)}]"

class BuildMapRepr (ts : List (Type u)) where
  build : MapRepr ts

instance : BuildMapRepr [] where
  build := MapRepr.nil

instance [Repr a] [BuildMapRepr as] : BuildMapRepr (a :: as) where
  build := MapRepr.cons (inferInstance : Repr a) (BuildMapRepr.build)

/- @@@
## MapShow: Printing Heterogeneous Tuples

A typesafe MapShowBundle type encodes
- input types as (e.g., [Nat, Bool, String])
- output types bs (e.g., [String, String, String])
- fs : HList (ZipWithFun as bs) — per-element function types
- xs : HList as — the input values
- bsInst : BuildMapRepr bs — so each type in bs has Repr instance for printing
@@@ -/
structure MapShowBundle (as bs : List (Type u)) where
  fs : HList (HList.ZipWithFun as bs)
  xs : HList as
  bsInst : BuildMapRepr bs


/- @@@
Takes a fully-typed MapShowBundle record and returns a String.
Returns the pretty-printed result of mapping the functions over the values.
@@@ -/
def mapShowBundle {as bs : List (Type u)} (b : MapShowBundle as bs) : String :=
  match HList.map b.fs b.xs with
  | some ys => toPrettyString ys b.bsInst.build
  | none => "mapping failed"

/- @@@
Pretty-print result of function map over an HList using inferred Repr
@@@ -/
def mapShow
  {as bs : List (Type u)} [BuildMapRepr bs]
  (fs : HList (HList.ZipWithFun as bs))
  (xs : HList as)
  : String :=
  match HList.map fs xs with
  | some ys => toPrettyString ys (BuildMapRepr.build)
  | none => "mapping failed"

/- @@@
## Example: Forming and Printing an HList of Values
@@@ -/

-- Functions of three different types to String
def f₁ : Nat → String := toString
def f₂ : Bool → String := fun b => if b then "yes" else "no"
def f₃ : String → String := String.toUpper

-- a type-heterogenous list of those three functgions
def fs : HList [Nat → String, Bool → String, String → String] :=
  HList.cons f₁ (HList.cons f₂ (HList.cons f₃ HList.nil))

-- a type-matched and -checked list of values (7, false, "hello")
def xs : HList [Nat, Bool, String] :=
  HList.cons 7 (HList.cons false (HList.cons "hello" HList.nil))

def myBundle : MapShowBundle [Nat, Bool, String] [String, String, String] where
  fs := fs
  xs := xs
  bsInst := inferInstance

def testMapped : String := mapShowBundle myBundle

#eval testMapped -- "[7, no, HELLO]"



/- @@@
### Example: Represent "configuration spaces"
@@@ -/

abbrev ConfigSchema := [Nat, Bool, String]

-- Sample config: max retries = 3, verbose = false, log file = "/tmp/log.txt"
def myConfig : HList ConfigSchema :=
  HList.cons
    3
    (HList.cons
      false
      (HList.cons
        "/tmp/log.txt"
        HList.nil
      )
    )

-- Extract components
def maxRetries := HList.head myConfig
def verbose := HList.head (HList.tail myConfig)
def logFile := HList.head (HList.tail (HList.tail myConfig))

#eval logFile   -- "/tmp/log.txt"
#eval verbose
#eval maxRetries

/- @@@
## Qualities and Tradeoffs

- typesafe
- dynamic length
- pattern matching
- but linear access time
- but uses Option (HList bs), avoiding totality checking on HList bs directly

It always typechecks because:
- It uses Option (HList bs), avoiding totality checking on HList bs directly.
- The last catch-all handles any mismatch safely.
- No unreachable! or panic! needed.
- The return type is always inhabited (Option is always inhabited).
@@@ -/

#eval testMapped

end DMT1.Lecture.hetero.hetero.HList
