/- @@@
# Induction

Can we easily imagine a function that computes
value of functions, such as factorial n, for *any*
natural number argument, n, from 0 all the way up.
As such a function consumes a natural number value
and returns another natural number value, it's type
must be *Nat → Nat*. But can we compute the value of
the function for *any* n?
@@@ -/

/- @@@
## A Manual Approach

First, we could fill in a table of function values
starting with, in the 0th row, n = 0 in the first
column, and the value of (factorial n), which is 1,
in the in the second column.

+---+-------+
| n |   n!  |
+---+-------+
| 0 |   1   |
| 1 |       |
| 2 |       |
| 3 |       |
| 4 |       |
| 5 |       |


Having thereby "initialized" the table, let's figure
out how to complete the second row. What do we know
at this point? What can we assume? We know that for
n = 0, n! = 1. Those entries are already in the table.
Now we need to compute 1!. We could say, we know it's
1, because someone told you, and just fill it in, but
it's better to find the general principal.

That principle (now that the table is initialized) is
that you can always fill in the right value in the next
row to be completed multiplying n (in the left column)
by the factorial of n' in the previous row (on right).

You do it. Fill in the answers in the table above.

Here's another easy computation that can help you to
start to think inductively:

- 5*4*3*2*1*1 =
- 5*(4*3*2*1*1) =
- 5*4!


So, to compute 5! for the right hand column in row n = 5,
you just multiply 5 by the result you must already have
for n' = 4. That's it, unless n = 0, in which case, the
answer is already there from the initialization.
@@@ -/

/- @@@
The preceding demonstration and analysis should leave you
convinced that in principle we could compute n! for any n.
Fill in the first row, then repeat the procedure to get the
answer for the next row until you've down that for rows all
the way up to n. In other words, do the base step to start,
then repeat the "inductive" step n times, and, voila, the
answer right there in the righthand column of the table.

That's pretty cool. To make use of it in computer science,
we need to formalize these ideas. Here we'll formalize them
in the logic of Lean, as propositional logic is too simple
to represent these rich ideas.
@@@ -/

/- @@@
## Specification: Base and Step Functions

So let's now look at what we're doing here with precision.

We envisioned a table. The rows are indexed (first column) by
natural numbers. The second row should contain the factorials
of these arguments. We don't really have to include the idea
of a table in our specification. The only really interesting
values are those in the second column, fac n.

So, first, we'll specify the value of fac n for the base case,
where n = 0. The value is one, and we'll call it facBase.
@@@ -/

def facBase := 1

/- @@@
Now comes the interesting part. To compute each subsequent
value, we repeatedly applied the same formula, just moving
the index up by one each time, and building a new answer on
the answer we already had for the preceding value of n (the
preceding row). What computation did we carry out exactly?
We represent it as a function, facStep.

Suppose we're trying to fill in the value for row n, where
n ≠ 0. As n ≠ 0, there is a natural number one less than n;
call it n'. Clearly n = n' + 1, and n' is the index of the
preceding row. We know we can fill in that table as high as
we want, so when we're trying to fill it in for some row, n,
we can *assume* that we known both n' (easy) and fac n', and
from those we can compute fac n.

Crucial idea: What do *assumptions* turn into in code? They
are *arguments* to other definitions. When you're writing a
function that will take two arbitrary arguments, a and b, and
combine them into a result in some what, what is your mindset
when you write the code? You *assume* that you actually have
two such arguments, and you write the code accordingly. It's
going to be the same for us. When you think of assumptions,
think of code from the perspective of someone who's writing
it. You can always assume something and then act accordingly.
This is what programmers do!

We thus turn the *assumptions* that we know n' and fac n'
when trying to compute fac n, into *arguments* to a function.
The person who "implements" the function assumes they get the
named values as arguments and then computes the right result
and returns it accordingly.
@@@ -/

def facStep : Nat → Nat → Nat
| n', facn' => (n' + 1) * facn'

-- Applying facStep to n' and fac n' yields fac n
-- The base case, that fac 0 = 1, gives us a place to start
--
--            n'   fac n'        n    fac n
#eval facStep 0   facBase   -- n = 1,   1
#eval facStep 1   1         -- n = 2,   2
#eval facStep 2   2         -- n = 3,   6
#eval facStep 3   6         -- n = 4,   24
#eval facStep 4   24        -- n = 5,   _

/- @@@
## Induction

Ok, that's all super-cool, and formalizing it in Lean has
let us to semi-automatically compute our way up to fac n
for any n. The crucial idea is: start with the base values
and then *apply the step function n times*, always feeding
it the results of the previous step, or the base values, as
the case may be.

Yes, that's fine, but how do we graunch our base and step
"machines" into a new machine, a function, that takes *any*
n and automatically computes n!? We'll, at this point, we
do not have a way, even in principle, to do this. Any yet
we're convinced that having base and step machines should
suffice for the construction of a machine that automates
what we just said: start with the base then step n times.

The answer is that we need, and have, a new principle: an
induction principle, here for the natural numbers. What it
says, semi-formally, is that if you have both a value of a
function, f, for n = 0, and you have a step function that
takes n' and f n' and returns f n, then you can derive and
then use a function that takes any n and returns f n for it.

You can think of the induction principle (for Nat) as
taking  two small machines--one that answers (f 0) and one
that takes any n' and f n' and answers (f n)--and that
combines them into a machine that takes any n and answers
(f n). In a nutshell, the induction principle automates
the process of first using the base machine then applying
the step machine n times to get the final answer.

In Lean, the induction principle (function!) in Lean for
the natural numbers is called Nat.rec.
@@@ -/

def fac : Nat → Nat := Nat.rec facBase facStep

/- @@@
Let's break that down. We are defining fac as the name of
a function that takes a Nat argument and returns a Nat
results. That's the type of the factorial function, as we
discussed above. The magic is on the right. The function
that fac will name is *computed* by passing the base value
and the step function to the induction function for Nats!

And by golly, it works.
@@@ -/

#eval fac 0   -- expect 1
#eval fac 1   -- expect 1
#eval fac 2   -- expect 2
#eval fac 3   -- expect 6
#eval fac 4   -- expect 24
#eval fac 5   -- expect 120

/- @@@
## Another Example

Compute the sum of all the natural numbers up to any n.

What is the sum of all the numbers from 0 to 0? It's zero.
Now specify your step function: a function that takes n' and
*sum* n' and that returns *sum n*. Finally, pass these two
"little machines" to the Nat.rec to get a function that will
work for all n. Then have fun!
@@@ -/

def baseSum := 0
def stepSum (n' sumn' : Nat) := (n' + 1) + sumn'
def sum : Nat → Nat := Nat.rec baseSum stepSum

-- Voila!
#eval sum 0   -- expect 0
#eval sum 1   -- expect 1
#eval sum 2   -- expect 3
#eval sum 3   -- expect 6
#eval sum 4   -- expect 10
#eval sum 5   -- expect 15


#check Nat.rec

/- @@@
Nat.rec.{u}
  {motive : Nat → Sort u}
  (zero : motive Nat.zero)
  (succ : (n : Nat) → motive n → motive n.succ)
  (t : Nat) :
  motive t
@@@ -/

#check List.rec

/- @@@
List.rec.{u_1, u} {α : Type u}
  {motive : List α → Sort u_1}
  (nil : motive [])
  (cons : (head : α) → (tail : List α) → motive tail → motive (head :: tail))
  (t : List α) :
  motive t
@@@ -/


/-  @@@
## Notation

From now on, think of induction as building
forward from a base case, at each step using
the results from previous steps as arguements
to step functions that compute results for the
next inputs up.

Moreover, when you're figuring out how to write
such a function don't just think of it this way
but write down your base value and inductive step
functions. What you no longer need deal with is
the awkward separate definition then combination
of the smaller machines.
@@@ -/

/- @@@
Let's break this definition down.

We define a function, sum', that returns the sum of
the natural numbers from 0 to any given argument, n.

This function is of coures of type Nat → Nat

The value to which "sum" will be bound is (of course)
a *function*, here specified to take an argument, n,
that then acts in one of two ways depending on whether
n is 0 (Nat.zero) or the successor (n' + 1) of some
one-smaller number (Nat.succ n').

The two cases here correspond directly to the two small
machines! In the case of n = 0, we return 0. In the case
n = n' + 1 (n greater than 0), we return (n' + 1) + sum n.
That is, we apply the step function to n' and sum n', just
as we did earlier. And it all works.
@@@ -/
def sum' : Nat → Nat :=
fun n => match n with
| Nat.zero => Nat.zero
| Nat.succ n' => Nat.succ n' + sum' n'

#eval sum' 0    -- expect 0
#eval sum' 5    -- expect 15

/-  @@@
## Lean preferred notation

When writing such definitions, however, it's preferred
to use Lean notations for natural numbers. This avoids
having to take extra steps when writing proofs later to
simply translate and forth between, say, 0 and Nat.zero.

So, instead of Nat.zero, write 0 in practice. And instead
of Nat.succ n', write (n' + 1). Here it is important that
the + 1 be on the right. When it is, Lean interprets it as
Nat.succ 1, whereas on the left it'd be Nat.add 1 n'. The
latter is *not* what you want in a case analysis pattern
where you intend to match with Nat.succ n' for some n'

So here's the cleaned up code you should actually write.
@@@ -/

def summ : Nat → Nat
| 0 => 0
| n' + 1 => (n' + 1) + summ n'

#eval summ 100

/- @@@
Lean's preferred notation for specifying such functions
really does involve specifying the two smaller machines.
Just look carefully at right sides of the two cases! The
base case is 0. On the right for the inductive case is the
step function! summ n = summ n' + 1 = (n' + 1) + summ n'.
@@@ -/

/- @@@
## Unrolling recursions

Ok, so the induction principle seems wildly useful, and it
is. It reduces the problem of writing a function for any n
to two simpler subproblems: one for base case (constant),
and one to define the step function. Then wrap them both up
using "the induction machine" to get a function that works
*automatically* for any n.

But, you ask, what actually happens at runtime? Well, let's
see! Here we iteratively evaluate the application of the *sum*
function to 5, to compute the sum of the numbers from 0 to 5,
which we can easily calculate to be 15. Be careful to read the
notes about which cases in the function definition the different
arguments match.
@@@ -/

/- @@@
sum 5                               -- matches n'+1 pattern; reduces to following:
5 + (sum 4)                         -- same rule: keep reducing nested applications
5 + (4 + (sum 3))                   --
5 + (4 + (3 + (sum 2)))             --
5 + (4 + (3 + (2 + (sum 1))))       --
5 + (4 + (3 + (2 + (1 + (sum 0))))) -- now reduce these expressions by addition
5 + (4 + (3 + (2 + (1 + 0))))       -- by apply Nat.add to 1 and 0
5 + (4 + (3 + (2 + (1))))           -- all the rest is just addition
5 + (4 + (3 + (3)))
5 + (4 + (6))
5 + (10)
15                                  -- the result for 5
@@@ -/

/- @@@
## Forget about unrolling recursions

Now that you've seen how a recursion unfolds during actual
computation, you can almost forget about it. The induction
principle for natural numbers is *valid* and can be used
and trusted: all you need to define are a base case and
a step function (of the kind required, taking n' and the
answer for n' as arguments and producing the answer for n),
and induction will iterate the step function n times over
the result from the "base function." The only "hard" job
for you is usually to figure out the right step function.
@@@ -/

/- @@@
## Exercises

### Sum of Squares of Nats Up To n

Define a function two ways: using Nat.rec applied to two
smaller "machines" (base value and step function), and
then using Lean's preferred notation as described above.
The function should compute the sum of the squares of all
the natural numbers from 0 to any value, n.

Start by completing a table, in plain text, just as we
presented above, but now for this function. As you fill
it in, pay close attention to the possibility of filling
in each row using the values from the previous row. That
will tell you what your step function will be.
@@@ -/


-- base value machine
def baseSq : Nat := 0

-- step up answer machine
-- from n' and sumSq n' return (n' + 1)^2 + sumSq n'
def stepSq : Nat → Nat → Nat
| n', sum_sq_n' => _

-- here's how the stepping up works
#eval stepSq 0 0  -- return answer for n = 1; expect 1
#eval stepSq 1 1 -- return answer for n = 2; expect 5
#eval stepSq 2 5 -- return answer for n = 3; expect 14
#eval stepSq 3 14 -- return answer for n = 4; expect 30
#eval stepSq 4 30 -- return answer for n = 5; expect 55

-- apply induction to construct desired function
def sumSq : Nat → Nat := Nat.rec baseSq stepSq

#eval sumSq 0   -- expect 0
#eval sumSq 1   -- expect 1
#eval sumSq 2   -- expect 5
#eval sumSq 3   -- expect 14
#eval sumSq 4   -- expect 30
#eval sumSq 5   -- expect 55  (weird: also sum of nat 0..10)

def sumSq' : Nat → Nat
| 0 => 0
| (n' + 1) => let n := n' + 1
              n^2 + sumSq' n'

#eval sumSq' 0   -- expect 0
#eval sumSq' 1   -- expect 1
#eval sumSq' 2   -- expect 5
#eval sumSq' 3   -- expect 14
#eval sumSq' 4   -- expect 30
#eval sumSq' 5   -- expect 55  (weird: also sum of nat 0..10)

/-  @@@
Format your table here
 @@@ -/

/-  @@@
Now write test cases as above, including "expect"
comments based on your table entries above, and be
sure your tests (using #eval) are giving the results
you expect. Example: sumSq 2 = 2^2 + 1^2 + 0^2 = 5.
@@@ -/

/- @@@
### Nat to BinaryNumeral

Define a function that converts any natural number n
into a string of 0/1 characters representing its binary
expansion. If n = 0, the answer is "0". If n = 1, the
answer is "1". Otherwise we need to figure out how to
deal with numbers 2 or greater.

Let's make a table

0 | "0"
1 | "1"
2 | "10"
3 | "11"
4 | "100"
5 | "101"
etc

What do we notice? The righmost digits flip from 0
to 1 to 0 to 1, depending on whether the number is
even or odd. Another way to think about it is that
if we divide the number by 2 and compute a remainder,
we get the rightmost digit. 4/2 = 0. 0 is the right
digit of "100". And 5/2 = 1, the rightmost digit of
"101". The remainder when dividing by 2 is also
called n mod 2, or n % 2 in many popular programming
languages.
@@@  -/

#eval 0 % 2
#eval 1 % 2
#eval 2 % 2
#eval 3 % 2
#eval 4 % 2
#eval 5 % 2

/- @@@
So given any n we now have a way to get its
rightmost digit in binary by taking the number
mod 2. As an aside, we can easily convert such
a 0/1 natural number to a string using toString.
@@@ -/

#eval toString 5

/-  @@@
But what about converting the rest of the input
to binary digits? What even is "the rest" of the
input. Well, in this case, it's n/2, right? When
we divide n by 2 using natural number arithmetic,
we get the quotient and thow away the remainder.
So let's look at how to covert 5 to a its binary
expansion.

| n | n/2 | n%2 | str |
|---|-----|-----|-----|
| 5 |  2  |  1  | "1" |
| 2 |  1  |  0  | "0" |
| 1 |  0  |  1  | "1" |
| 0 |  0  |  0  | ""  |

At each step, we get the right most digit using %2
and we get the rest of the number to covert on the
left of that last binary digit (bit) using /2. We're
done at the point where the number being converted is
0, for which we return "". Finish the definition of
the function here, and write test cases for n up to
5 to see if it appears to be working.

By the way, you can append to strings in Lean using
the String.append function, with notation, ++.
 @@@ -/

#eval "10" ++ "1"

/- @@@ Complete this function definition using preferred
notation based on your known base and step "machines".
We provide most of an answer. *Do not guess*. Figure
it out! After the ++ comes the length-one "0" or "1"
string for the rightmost digit in the binary numeral.
What completes the answer by appearing to the left
of the ++ ((String append)?
 @@@ -/

def binaryRep : Nat → String
| 0 => "0"
| 1 => "1"
| n' + 2 => let n := n' + 2
            _ ++ toString (n % 2)

-- Complete the definition. The tests will work,.
#eval binaryRep 0   --expect "0"
#eval binaryRep 5   --expect "101"

/- @@@
### Other Induction Axioms

Interesting. We've got ourselves a recursive
function, but it doesn't quite fit the schema
we've seen to now. Nat.rec allows us to build
a general purpose function from a machine that
returns an example for *one* based case and a
machine that builds an answer for n = (n' + 1)
from the one for n' (which is obviously n - 1).
But in our function, we construct an answer for
n (for n ≥ 2) from an answer for n/2, not n-1.
It works but it won't work to pass this kind of
step function to Nat.rec.

As you might guess there are several induction
axioms. The form we've studied lets you assume
that when computing an answer for n = (n' + 1)
that you can assume you have n' and the answer
for n'. From those you compute the answer for n.

A different form of induction let's you assume
when computing an answer for n that you have n'
and answers for all values from n' down to the
base value, here 0.

We have implicitly used this other axiom in
this case, as we're accessing an answer "earlier"
in our table, but not at position n - 1, rather
at position n / 2. The string representation of
that will be all of the binary digits to the left
of the final digit, determined separately by the
remainder, n % 2.

When we write recursive functions in practice,
we can usually assume access to answer for *all
smaller" values of n' (e.g., lesser by one, or
quotient by 2), by way of recursive calls with
these values as actual parameters.
@@@ -/

/-  @@@
### Specifying the Fibonacci Function

Haha. So we finally get to the exercise. You
are to specify in Lean and test a function to
compute values of the Fibonacci function for any
Nat argument, n. Here's how you might see it
defined in a book.

For 0, fib should answer 0
For 1, fib should answer 1
For any n = (n' + 2), fib should answer fib n' + fib (n' + 1)

You can see here that the definition assumes that
when computing an answer for n, that answers are
available for both fib n' [fib (n - 2)] as well as
for fib (n' + 1) [fib (n - 1)]. Nat.rec won't work
here.  Just use the recommended syntax and notations
for writing such functions.

Oh, the table. It helps! Fill in enough answers to
grok it! Complete the table in your notes.

|  0  |  0  |
|  1  |  1  |
|  2  |  1  |
|  3  |  2  |
|  4  |  3  |
|  5  |  5  |
|  6  |  8  |
|  7  | 13  |
|  8  | __  |
|  9  | __  |
| 10  | __  |

You see how you build an answer for n from answer not
just one but both one and two rows back.

Final hint: Define two base cases, for n = 0 and n = 1, then a
third case for the indutive construction, for any n = (n' + 2).
@@@ -/

def fib : Nat → Nat
| 0 => _
| 1 => _
| n' + 2 => _

/- @@@
Write test cases for 0, 1, 2, and 10. Does it work?
 @@@ -/

/- @@@
What we see in the definition of the Fibonacci function
are two base cases and a "step" function that uses the
results of the prior *two* computations for all inputs
greater than or equal to two.

The Nat induction principle we've see up to now does
not rely on multiple prior values. This function does.
So it must be using a different notion of induction,
and that's exactly right. In strong induction, at each
step one can assume one has not only the result for the
immediately preceding argument, but for the answers for
*all* prior argument values.

The Fibonacci function is a special case. It assumes it
has, and it uses, the prior *two* outputs to compute the
output for the next larger input value. The variant of
simple induction (for Nat values) used here is called
*strong induction*. We're not yet prepared to use it
directly to define recursive functions like *fib*, but
you should now be able at least to read and understand
it. Your assignment here, then, is simply to express
the formal definition in easy to understand English.
In Lean, strong induction is supported (for Nat) by
the axiom called *Nat.strongRecOn*.
@@@ -/

--
#check Nat.strongRecOn

open Nat
