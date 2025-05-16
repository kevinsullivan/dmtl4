
# Heterogeneous Collections (Lists, Tuples, etc.)

DRAFT: STILL DEVELOPING.

So far we have seen parametric polymorphism, which enables
the definition of terms that can be parameterized to deal with
different types of objects. For example, we have the polymorphic
type, *List (α : Sort u)*, supportings lists of objects of any
given *single* type.

Sometimes, however, we want to represent a collection of elements
of varying, or *heterogeneous*, types. Suppose, for example, that
we want to represent the possible signatures of procedures in some
language. A typical type signature comprises a list of the types of
the formal parameters of the procedure, and at any call site, one
must provide a list of actual parameter values that *type checks*
against that list of types.

The goal of this chapter is to present a range of approaches to
specifying such heterogeneous collections of values. We present
six somewhat different methods. We briefly summarize strengths and
weaknesses of each approach and potential use cases to which each
approach is well matched.

<!-- toc -->

```lean
namespace DMT1.Lecture.hetero.hetero
```

## Heterogeneous Lists (HList)

```lean
universe u
inductive HList : List (Type u) → Type (u+1) where
  | nil : HList []
  | cons {α : Type u} {as : List (Type u)} : α → HList as → HList (α :: as)

-- Example HList: [Nat, Bool, String]
def myHList : HList [Nat, Bool, String] :=
  HList.cons 42 (HList.cons true (HList.cons "hello" HList.nil))

namespace HList

-- Accessor functions
def head {α : Type} {as : List Type} : HList (α :: as) → α
  | cons x _ => x

def tail {α : Type} {as : List Type} : HList (α :: as) → HList as
  | cons _ xs => xs

-- Example access
#eval head myHList                           -- 42
#eval head (tail myHList)                   -- true
#eval head (tail (tail myHList))            -- "hello"

end HList

-- Used for argument list for a function expecting [Nat, Bool, String]
def exampleArgs : HList [Nat, Bool, String] :=
  HList.cons 42 (HList.cons true (HList.cons "hello" HList.nil))

-- Accessing values
#eval HList.head exampleArgs          -- 42
#eval HList.head (HList.tail exampleArgs)  -- true
```


Ot to represent configuration spaces and points within them.

```lean
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

#eval logFile  -- "/tmp/log.txt"
```

- typesafe
- dynamic length
- pattern matching
- linear access time


## Finite-Index Signature Tuples (Fin n → σ i)

```lean
def Sig (n : Nat) := Fin n → Type
def Val (σ : Sig n) := ∀ i : Fin n, σ i
```

- structured argument lists
- C++-like parameter packs

- index-, not pattern-matching-based, access
- dependent typing

- function signatures (heterogeneous argument modeling).
- tatically typed, fixed arity tuples with per-index types

-- TODO: Examples


## Dependent Pair (Sigma) Chains

Idea: Use Σ i, σ i recursively for list-like collections.
Here we convert an n-Sig to such a Type by recursion on n.

```lean
-- A heterogeneous n-tuple based on a type signature σ : Fin n → Type
def HChain : (n : Nat) → (σ : Sig n) → Type
  | 0,     _ => Unit
  | n + 1, σ => Σ x : σ ⟨0, Nat.zero_lt_succ n⟩,
                HChain n (fun i => σ ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩)

-- TODO: Examples
```

Type-safe with different types per position
Good for modeling recursive structures or sequences
Hard to work with.
No constant-time access
Not supportiveo of size-polymorphism
Niche use in specific induction-based constructions.

## Existential Wrapping (Σ α, α) or Custom Dyn Types

```lean
inductive MyDyn where
  | nat : Nat → MyDyn
  | str : String → MyDyn
  | bool : Bool → MyDyn
-- or use: Σ (α : Type), α

-- TODO: Examples
```

- Store heterogeneous values in (List MyDyn).
- Useful with JSON-style serialization [or dynamic programming]
- Loses static type information.
- Must downcast to use values — potentially unsafe unless carefully checked.
- Dynamic modules or configurations.
- Interfacing with external data or plugin systems.


## Dependently Typed (Heterogeneous) Vectors

```lean
inductive DVec : (n : Nat) → (σ : Fin n → Type u) → Type (u + 1)
  | nil {σ : Fin 0 → Type u} : DVec 0 σ
  | cons {n : Nat} {σ : Fin (n + 1) → Type u} :
      σ 0 →
      DVec n (fun i => σ (Fin.succ i)) →
      DVec (n + 1) σ

def DVec.get {n : Nat} {σ : Fin n → Type u} (xs : DVec n σ) (i : Fin n) : σ i :=
  match xs, i with
  | DVec.cons x _, ⟨0, _⟩     => x
  | DVec.cons _ xs', ⟨i'+1, h⟩ =>
      xs'.get ⟨i', Nat.lt_of_succ_lt_succ h⟩

def mySig : Fin 3 → Type
  | ⟨0, _⟩ => Nat
  | ⟨1, _⟩ => Bool
  | ⟨2, _⟩ => String

def myDVec : DVec 3 mySig :=
  DVec.cons (42 : Nat) (DVec.cons true (DVec.cons "hello" DVec.nil))

#eval myDVec.get ⟨0, by decide⟩  -- 42
#eval myDVec.get ⟨1, by decide⟩  -- true
#eval myDVec.get ⟨2, by decide⟩  -- "hello"


open DVec

def DVec.reprDVec {n : Nat} {σ : Fin n → Type u} (inst : ∀ i, Repr (σ i)) :
    DVec n σ → String
  | DVec.nil => "[]"
  | @DVec.cons n' σ' x xs =>
    let head := Std.Format.pretty (repr x)
    let tail := DVec.reprDVec (fun i => inst (Fin.succ i)) xs
    "[" ++ head ++ "," ++ tail.dropWhile (· == '[')   -- TODO: extra , after last elt

instance {n : Nat} {σ : Fin n → Type u} [∀ i, Repr (σ i)] : Repr (DVec n σ) where
  reprPrec xs _ := Std.Format.text (DVec.reprDVec (inst := inferInstance) xs)

instance {n : Nat} {σ : Fin n → Type u} [∀ i, Repr (σ i)] : ToString (DVec n σ) where
  toString xs := DVec.reprDVec (inst := inferInstance) xs
```

Lean does not synthesize ∀ i, Repr (σ i) even if it knows each Repr (σ i)
separately. We help it by hand-writing the dependent function instance.
```lean
instance : ∀ i : Fin 3, Repr (mySig i)
  | ⟨0, _⟩ => inferInstanceAs (Repr Nat)
  | ⟨1, _⟩ => inferInstanceAs (Repr Bool)
  | ⟨2, _⟩ => inferInstanceAs (Repr String)

#eval myDVec
```

-Precise and compositional
- Access by Fin i
- Allows index-aligned computations
- Boilerplate-heavy
- Requires dependent recursion for construction and access
- Good for index-typed languages, embedded DSLs, typed syntax trees

## Records with Varying Fields

Instead of a positional heterogeneous list (like HList or DVec), this
approach represents structured heterogeneous data by defining a record
with dependent or polymorphic fields — each possibly with a different
type.

- Good for
  - modeling modules or plugins
  - representing records with named fields and varying types
  - building extensible systems using Σ-types or type-class–based field access

```lean
def Args {n : Nat} (σ : Sig n) := ∀ i : Fin n, σ i
```

Now we can specify a self-describing heterogeneous record that it carries
its own field types (the signatureσ) and corresponding values (the args).
```lean
structure ModEntry where
  {n : Nat}
  σ : Sig n
  args : Args σ


def aSig : Sig 3
  | 0 => Nat
  | 1 => String
  | 2 => Bool

def anArgs : Args aSig
  | 0 => (42 : Nat)
  | 1 => "hello"
  | 2 => true

def entry1 : ModEntry := { σ := aSig, args := anArgs }

#eval entry1.args (0 : Fin 3)  -- 42 : Nat
#eval entry1.args (1 : Fin 3)  -- "hello" : String
#eval entry1.args (2 : Fin 3)  -- true : Bool
```

- Extensible: you can build lists of ModEntry, each with different signatures
- Type-safe: each Args σ is type-safe by construction
- Dynamic access: you can store these in dynamic registries
- Good for reflection, serialization, plugin systems


```lean
-- #eval repr entry1
-- #eval toString entry1

end hetero
```
