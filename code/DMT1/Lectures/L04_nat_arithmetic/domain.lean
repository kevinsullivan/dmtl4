namespace DMT1.Lectures.L04_nat_arithmetic.domain

/- @@@


# Domain: natural number arithmetic

## The Nat Type

We use Lean's definition of the Nat type.
@@@ -/

#check Nat

/- @@@
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
@@@ -/

def z : Nat := Nat.zero
def o : Nat := Nat.succ Nat.zero
def o' : Nat := Nat.succ z
def th : Nat := Nat.succ (Nat.succ (Nat.succ Nat.zero))

/- @@@


## Operations

### Unary Operations
@@@ -/

def id : Nat → Nat
| n => n

def inc : Nat → Nat
| n => Nat.succ n       -- Nat.succ n

def pred : Nat → Nat
| 0 => 0        -- Nat.zero
| Nat.succ n' => n'  -- Nat.succ n'

def pred2 : Nat → Nat
| 0 => 0
| 1 => 0
| Nat.succ (Nat.succ n'') => n''


#eval pred 0
#eval pred2 0
#eval pred2 2
#eval pred2 5


def dec : Nat → Nat := pred     -- read this carefully and understand it

def fac : Nat → Nat
| 0 => 1
| (Nat.succ n') => (Nat.succ n') * fac n'


inductive Tree : Type
| empty
| node (n : Nat) (l r : Tree)

def size : Tree → Nat
| Tree.empty => 0
| Tree.node _ l r => 1 + size l + size r

def sum : Tree → Nat
| Tree.empty => 0
| Tree.node n l r => n + sum l + sum r

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

Predicates represent *properties* of objects or tuples of
objects. Here we represent several predicates on individual
(unary) and pairs of (binary) natural numbers. The first,
isEven, indicates whether a given number "has the property
of being zero", for example.

### Unary Predicates
@@@ -/

def isZero : Nat → Bool
| 0 => true
| _ => false

def isEven : Nat → Bool
| 0 => true
| 1 => false
| n'' + 2 => isEven n''

def isOdd : Nat → Bool
| n => !(isEven n)


/- @@@
### Binary Predicates

We also define several binary (two-argument) predicates on the
natural numbers, representing these predicates as functions from
pairs of natural numbers to Boolean.
@@@ -/

def eq : Nat → Nat → Bool
| 0, 0 => true
| 0, _ => false
| _, 0 => false
| (n' + 1), (m' + 1) => eq n' m'

def le : Nat → Nat → Bool
| 0, _ => true
| (_ + 1), 0 => false
| (n' + 1), (m' + 1) => le n' m'

def gt : Nat → Nat → Bool
| n, m => ¬ le n m

def lt : Nat → Nat → Bool
| n, m => le n m && !(eq n m)

def ge : Nat → Nat → Bool
| n, m => gt n m || eq n m

end DMT1.Lectures.L04_nat_arithmetic.domain
