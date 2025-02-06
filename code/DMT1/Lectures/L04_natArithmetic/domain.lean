import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation

namespace DMT1.Lectures.L04_natArithmetic.domain

/- @@@
# Domain: natural number arithmetic

## The Nat Type

We use Lean's definition of the Nat type.
@@@ -/

#check Nat

/- @@@
The Nat type defines terms that we understand
to represent natural numbers. Nat.zero represents
0, while Nat.succ, applied to any Nat value, n,
represents the natural number n + 1.

inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
@@@ -/

-- Examples of such terms
def z : Nat := Nat.zero
def o : Nat := Nat.succ Nat.zero
def o' : Nat := Nat.succ z
def th : Nat := Nat.succ (Nat.succ (Nat.succ Nat.zero))

/- @@@
Lean provides sophisticated built in support
for concrete notations (base 10 numerals) for
natural numbers. The natural numbers that we
represent in base 10 as 0, 1, and 3 can thus
be written in just this way in Lean: as 0, 1,
and 3. But you should now see these numerals,
in Lean, as de-sugaring to terms of type Nat.
@@@ -/

#reduce 0   -- Notation for Nat.zero
#check 1    -- Notation for (Nat.succ Nat.zero)


/- @@@
## Nat Operations

We will use the term, operations, here to refer
to functions from one or more natural numbers to
natural number results. That is, operations, in
our lexicon, will refer to what in algebra are
known as *endomorphisms*, which is the name used
for functions that map elements from a given set
back into the same set.

### Unary Operations

Here are straightforward definitions of three unary
operations: the identity function, the increment (++)
function, and the predecessor function, which does the
usual thing unless applied to 0 in which case it just
returns 0 itself, as there's no small Nat value that
it could return.

The concept to focus on here is *pattern matching* and
its use to *destructure* terms of the Nat type so that
desired results can be returned. The *id* function does
not need to destructure its argument. Nor does *inc.*
But when applied to any non-zero Nat term the *dec*
function matches the incoming argument as the successor
of some number; that number is temporarily given the
name, *n'*, and that is the value that the function
then returns.
@@@ -/

def id : Nat → Nat
| n => n

def inc : Nat → Nat
| n => Nat.succ n       -- Nat.succ n

def pred : Nat → Nat
| 0 => 0        -- Nat.zero
| Nat.succ n' => n'  -- Nat.succ n'

/- @@@
Pattern matching can do more than to strip away
a single constructor application to reveal, and
name, the terms that were its arguments. Here is
*pred2*, a function that for 0 or 1 returns 0 but
that for any argument greater than 1 returns two
less than that number. It does this by matching
on two Nat.succ applications, given a name to the
nat was the argument to the second, and returning
that value. (Note: *pred* is short for predecessor,
and is unrelated to *predicates*.)
@@@ -/

def pred2 : Nat → Nat
| 0 => 0
| 1 => 0
| Nat.succ (Nat.succ n'') => n''

-- Example applications
#eval pred 0
#eval pred2 0
#eval pred2 2
#eval pred2 5

-- Just defining *dec* as another name for *pred*
def dec : Nat → Nat := pred


/- @@@
### Recursively Defined Operations
A recursive definition of a function to compute the
factorial of any given natural number.
@@@ -/
def fac : Nat → Nat
| 0 => 1
| (Nat.succ n') => (Nat.succ n') * fac n'

/- @@@
### Binary Operations
@@@ -/

def add : Nat → Nat → Nat
| n, 0 => n
| n, (m' + 1) => (add n m') + 1

def sub : Nat → Nat → Nat
| 0, _ => 0
| n, 0 => n
| (n' + 1), (m' + 1) => sub n' m'

def mul : Nat → Nat → Nat
| _, 0 => 0
| n, (m' + 1) => add n (mul n m')

def exp : Nat → Nat → Nat
| _, 0 => 1
| n, (m' + 1) => n * exp n m'

/- @@@
## Predicates

A predicate is a *parameterized proposition.* In
other words, predicates are applied to arguments,
and they then reduce to propositions that might
or might not be true *about* those arguments. As
an example, a predicate called *isEven* could take
an argument, say *n*, and return the *proposition*
that *n%2 = 0%. This proposition is true for some
values of *n*, such as 0, 2, and 4, but not true
for other values, such as 1, 3, and 5.
@@@ -/

def isEven : Nat → Bool := λ n => n % 2 = 0

/- @@@
Predicates are *applied* to arguments. They are
literally thus functions of a sort, which you can
see clearly here, where *isEven* is defined to be
a function that takes an argument, *n*, and then
reduces (in Lean evaluates to) n % 2 = 0, which
in turn reduces to the Boolean value, *true*.
@@@ -/

#reduce isEven 4

/- @@@
Predicates can be understood as formally defining
*properties* of objects of a certain kind. Here the
*isEven* predicate expresses the *property* of "being
even." When a predicate takes multiple arguments, it
can be understood as defining a property of *tuples*
of values. For example, *equals* is a predicate taking
two arguments, call them *p* and *q* of some type, and
defines the property of those numbers being equal. As
a first example, consider a predicate that defines the
property of any number, *n*, being equal to zero. This
is a *unary* predicate on natural numbers.

### Unary Predicates
@@@ -/

def isZero : Nat → Bool
| 0 => true
| _ => false

#reduce isEven 0    -- expect true
#reduce isEven 1    -- expect false
#reduce isEven 2    -- expect true
#reduce isEven 3    -- false

/- @@@
There are often multiple ways to specify the same
predicate. Here's another definition of *isEven* as
a recursive, function. For 0 it returns true; for 1,
false; and for any larger number n, it returns the
answer for n-2, eventually reaching either the first
or the second base case.
@@@-/

def isEven' : Nat → Bool
| 0 => true
| 1 => false
| n'' + 2 => isEven n''


/- @@@
And here's a concise definition of the property of
being odd. Because we've represented predicates as
Lean functions, we can actually run them to compute
whether a given object has a given propert, getting
the answer as a value of type Bool.
@@@-/
def isOdd : Nat → Bool
| n => !(isEven n)


/- @@@
### Binary Predicates

Returning to the semantic domain of natural number
arithmetic, we now define the basic binary predicates,
also called relational operators, on natural numbers.
ASSIGNMENT: Study each definition; and to test your
understanding, erase it then recreate it.

These examples illustrate another important point: we
can use predicates to represent *relations* on objects.
Each of the following definitions formalizes a binary
relation on natural numbers: the *less than or equal
to* relation, along with others. Each predicate defines
the condition that a *pair* of numbers must satisfy to
be consider *in* the given relation.
@@@ -/

-- Equality of Natural numbers
def eq : Nat → Nat → Bool
| 0, 0 => true
| 0, _ => false
| _, 0 => false
| (n' + 1), (m' + 1) => eq n' m'

-- The less than or equal
def le : Nat → Nat → Bool
| 0, _ => true
| (_ + 1), 0 => false
| (n' + 1), (m' + 1) => le n' m'

-- greater than
def gt : Nat → Nat → Bool
| n, m => ¬ le n m

-- less than
def lt : Nat → Nat → Bool
| n, m => le n m && !(eq n m)

-- greater than or equal
def ge : Nat → Nat → Bool
| n, m => gt n m || eq n m

/- @@@
As a final point, in anticipation of
developments to come, we can similarly
view a *unary* predicate as defining not
just a *property* of objects of a given
kind, but a *set* of all objects of that
type, namely the ones that satisfy the
predicate, which can call a *membership
predicate*. Indeed, this is exactly how
we will not only specify but represent
sets in Lean. Before we can formalize
this idea, we'll need to see how to
define predicates *logically* in Lean,
rather than *computationally* as we've
done here. Computational representations
can be run to *computate* the truth of
a proposition such as *isEven 3*, whereas
the application of a logical definition
of a predicate to argument reduces to a
proposition for which determination of its
truth requires a *proof*. We address such
issues a little later in this book. Here,
though, is a preview.
@@@ -/

-- Logical definition of the set of even numbers
def evens : Set Nat := { n : Nat | isEven n}

-- The logical proposition that 4 is even
def fourEven := 4 ∈ evens

-- That proposition and a proof of it.
example : 4 ∈ evens := by rfl

/- @@@
For now, you know how to represent predicates as
functions. You can call them *predicate functions*
if you wish. This is how you'd typically express
predicates in an ordinary programming language,
such as C, Python, or Java, that doesn't have any
notion or support for logical reasoning. In Lean,
functions must be total, but not every predicate
can be expressed as a total function. Consider the
predicate *halts* that takes an C program as it
argument and returns true iff and only if there
is no input on which the program can go into an
infinite loop. In Lean we will be forced instead
to represent such predicates *logically*. We will
no longer be able to compute whether a given object
(such as a program) has a given property (halts on
all inputs), but will instead have to construct a
proof of that proposition for any given program.
@@@ -/
end DMT1.Lectures.L04_natArithmetic.domain
