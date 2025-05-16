/- @@@

# Heterogeneous Collections (Lists, Tuples, etc.)

EARLY DRAFT: STILL DEVELOPING.

We've seen that parametric polymorphism enables specialization
of definitions for argument values of any type, given as the value
of a formal parameter, (α : Type u). Such a specialized definition
then pertains and applies to values of any given actual parameter
values of that that type, but only of that type. For this construct
to work well, the fixed code of such a parameterized definition has
to work for objects of any type. The code cannot encode special case
logic for different types of objects. In Lean, one cannot match on,
which is to say, distinguish, different types at all. That would
make the logic unsound. Details on that can be found elsewhere.

Constructs like these are good for representing type-homogenous
definitions. For example, (List Nat) is the type of lists all of
the elements of which are necessarily, in this case, Nat. The
generalization of this special case is (List (α : Type u)), where
α is the type of *all* elements in any list value of type (List α).

Parametric polymorphism provides a lot of leverage, but is has its
limits. Sometimes we want to generalize concepts, such as addition,
for example, following certain intuitive rules, over objects of ad
hoc types. For example, we might want a function that implements
*add* for *Nats* and, of course, a necessarily different function
that implements *add* for Rats. We've already seen that overloading
of proof-carrying structures enables compelling formalizations of
at least some useful parts of the universe of abstract mathematics.
There's ample evidence from others

With typeclasses defined to capture the abstract concepts and their
instances providing implementations of these concepts for different
types of underlying objects, and with a notation definition, we can
write both (2 + 3) and ("Hello" + "world"), with  Lean figuring out
which instance implements + (add) for Nat, and which, for String.

These method provide a form of polymorphism narrower in range than
the parametric variety, insofar as one needs to implement the full
concept for each type of underlying object (e.g., Nat or String).
But is eliminates the constraint to uniformity of implementation,
and thereby greatly augments one's expressive power.

In the context of our encounter with typeclasses, instances, and
their applications in basic abtract algebra, we met another break
from type homogeneity, in vivid distinctions between homogenous
and homogeneous variants of the "same (and even more abstracted)"
concept. Addition of two scalars is type-homogenous, but addition
of a vector to a point is heterogeneous. In the formalization we
get from Lean, one version of the addition concept (+) is defined
by the Add, with Add.add taking and returning values of one type,
whereas the other (+ᵥ) is required to be used for addition of an
object of one type to an object of another, as in the case of
vector-point addition in affine spaces. Heterogeneity of this kind
is achieved through typeclass definitions parametrically polymorphic
in multiple types.

In this chapter we consider type heterogeneity in finite collections
of objects, such as lists or tuples represented as functions from a
natural number index set to the values at those indices. What if we
want a different type of value at each position in a tuple? It's not
a remotely crazy idea: we have databases full of tables with columns
having different types of data in them. It would be good to be able
to ensure that records (tuples of values) have corresponding types.
For example, if the type labels on columns were Nat, String, Bool,
we'd want to type-check corresonding value tuples, e.g., accepting
(1, "hi", true) but rejecting anything not a 3-tuple of values of
the specified types. Another application could be in representing
function type signatures and type-checked constructors for actual
parameteter value tuples.

AI Disclosure: The author did interact with ChatGPT, with context
provided by earlier, unrelated chats, when deciding how to populate
and organize parts of this chapter. I did adopt--and in most cases
fixed--some elements of the chat output. One cannot know the real
provenance of such outputs. I take responsibility for checking of
correctness. Should you recognize some clear derivative of your
own work in this chapter, please don't hesitate to let me know.

With that long intruction, the rest of this chapter presents six
somewhat different attacks on the same basis problem, noting some
of the strengths, weaknesses, and use case of each approach (that
right there does sound like ChatGPT, doesn't it).
cases.

<!-- toc -->
@@@ -/

namespace DMT1.Lecture.hetero.hetero

/- @@@
## Heterogeneous Lists (HList)
@@@ -/

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


/- @@@
Ot to represent configuration spaces and points within them.
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

#eval logFile  -- "/tmp/log.txt"

/- @@@
- typesafe
- dynamic length
- pattern matching
- linear access time
@@@ -/


/- @@@
## Finite-Index Signature Tuples (Fin n → σ i)
@@@ -/

def Sig (n : Nat) := Fin n → Type
def Val (σ : Sig n) := ∀ i : Fin n, σ i

/- @@@
- structured argument lists
- C++-like parameter packs

- index-, not pattern-matching-based, access
- dependent typing

- function signatures (heterogeneous argument modeling).
- tatically typed, fixed arity tuples with per-index types

-- TODO: Examples
@@@ -/


/- @@@
## Dependent Pair (Sigma) Chains

Idea: Use Σ i, σ i recursively for list-like collections.
Here we convert an n-Sig to such a Type by recursion on n.
@@@ -/

-- A heterogeneous n-tuple based on a type signature σ : Fin n → Type
def HChain : (n : Nat) → (σ : Sig n) → Type
  | 0,     _ => Unit
  | n + 1, σ => Σ x : σ ⟨0, Nat.zero_lt_succ n⟩,
                HChain n (fun i => σ ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩)

-- TODO: Examples

/- @@@
Type-safe with different types per position
Good for modeling recursive structures or sequences
Hard to work with.
No constant-time access
Not supportiveo of size-polymorphism
Niche use in specific induction-based constructions.
@@@ -/

/- @@@
## Existential Wrapping (Σ α, α) or Custom Dyn Types
@@@ -/

inductive MyDyn where
  | nat : Nat → MyDyn
  | str : String → MyDyn
  | bool : Bool → MyDyn
-- or use: Σ (α : Type), α

-- TODO: Examples

/- @@@
- Store heterogeneous values in (List MyDyn).
- Useful with JSON-style serialization [or dynamic programming]
- Loses static type information.
- Must downcast to use values — potentially unsafe unless carefully checked.
- Dynamic modules or configurations.
- Interfacing with external data or plugin systems.
@@@ -/


/- @@@
## Dependently Typed (Heterogeneous) Vectors
@@@-/

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

/- @@@
Lean does not synthesize ∀ i, Repr (σ i) even if it knows each Repr (σ i)
separately. We help it by hand-writing the dependent function instance.
@@@ -/
instance : ∀ i : Fin 3, Repr (mySig i)
  | ⟨0, _⟩ => inferInstanceAs (Repr Nat)
  | ⟨1, _⟩ => inferInstanceAs (Repr Bool)
  | ⟨2, _⟩ => inferInstanceAs (Repr String)

#eval myDVec

/- @@@
-Precise and compositional
- Access by Fin i
- Allows index-aligned computations
- Boilerplate-heavy
- Requires dependent recursion for construction and access
- Good for index-typed languages, embedded DSLs, typed syntax trees
@@@ -/

/- @@@
## Records with Varying Fields

Instead of a positional heterogeneous list (like HList or DVec), this
approach represents structured heterogeneous data by defining a record
with dependent or polymorphic fields — each possibly with a different
type.

- Good for
  - modeling modules or plugins
  - representing records with named fields and varying types
  - building extensible systems using Σ-types or type-class–based field access
@@@ -/

def Args {n : Nat} (σ : Sig n) := ∀ i : Fin n, σ i

/- @@@
Now we can specify a self-describing heterogeneous record that it carries
its own field types (the signatureσ) and corresponding values (the args).
@@@ -/
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

/- @@@
- Extensible: you can build lists of ModEntry, each with different signatures
- Type-safe: each Args σ is type-safe by construction
- Dynamic access: you can store these in dynamic registries
- Good for reflection, serialization, plugin systems
@@@ -/

-- TODO: Broken
-- #eval repr entry1
-- #eval toString entry1

end hetero
