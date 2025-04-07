import Mathlib.Data.Rel
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Real.Basic

namespace DMT1.Lectures.setsRelationsFunctions.relations



/- @@@
# Binary Relations

<!-- toc -->

Just as a set can be viewed as a collection of
individual objects of some type, α, specified by a
membership predicate on α, so we will now view at
a *binary relation* on α and β as a collection of
ordered pairs of objects, ( a : α, b : β ). It is
standard practice to specify y such relation with
a two-argument predicate on α and β, satisfied by
any pair of objects, *a* and *b*, that is defined
to be *in* the relation, and otherwise not.
@@@ -/

/- @@@
## Specification and Representation as Predicates

You'll recall from the section on sets that we not
only specify sets with membership predicates, but
that Lean also represents sets as unary predicates.
It thus defines the type, (Set α), as *α → Prop*.
Not every predicate is meant to represent a set,
so Lean provides the (Set α) definition so that
our code expresses the intended abstraction when
we mean for such a predicate to represent a set.
@@@ -/

variable
  {α : Type}
  {β : Type}

-- Again, sets are represented as predicates in Lean
#reduce (types := true) (Set α)     -- α → Prop
-- The type, Set α, is defined as the type α → Prop
-- (types := true) tells Lean to reduce types

/- @@@
## Rel α β: The Type of Binary Relations From α to β

It is also commplace to specify binary relations as
binary predicates. Moreover, just as Lean typically
represents sets as unary predicates, it represents
binary relations as binary predicates. To this end,
Lean defines *(Rel α β)* as *α → β → Prop*, as the
type of binary relation from objects of type α to
objects of type β.
@@@ -/

#reduce (types := true) Rel α β -- is α → β → Prop

/- @@@
## Example: The Relation \{ (0, 1), (1, 1), (1, 0) \}

Let's consider a simple example, of a finite binary
relation on the natural numbers. In this example we
will bypass *Rel Nat Nat* and use *Nat → Nat → Prop*
to make it clear that all we're really dealing with
are two-argument predicates.

Suppose we want to specify and represent the relation,
let's call it *tiny*, with the following pairs: { (0,1,),
(1,1), (1,0) }. We do this by defining the membership
predicate satisfied by all and only these pairs.
@@@ -/

def tinyMembershipPred : Nat → Nat → Prop :=
  fun fst snd =>
    fst = 0 ∧ snd = 1 ∨
    fst = 1 ∧ snd = 1 ∨
    fst = 1 ∧ snd = 0

/- @@@
When applied to a pair of Nat values, this
membership predicate yields a proposition about
the given pair of values that might or might not
be true. If it's true, that proves the pair is in
the relation. If it's false, that proves the pair
is not in the relation.

Fr example, applying tiny it to the pair of values,
such as 1 and 1, produces a a proposition, computed
by substituing the actual parameters (1 and 1) for
the formal parameters (fst, snd) in its definition.
Here we ask Lean to do this reduction for us. To
see the result, hover over #reduce or use Lean's
InfoView panel.
@@@ -/

#reduce (types := true) tinyMembershipPred 1 1
/- @@@
    1 = 0 ∧ 1 = 1 ∨
    1 = 1 ∧ 1 = 1 ∨
    1 = 1 ∧ 1 = 0
@@@ -/

example : tinyMembershipPred 1 1 := Or.inr (Or.inl (And.intro rfl rfl))

/- @@@
We can now define tiny as a binary relation on Nat,
giving *tinyMembershipPred* as the specification of
its membership predicate.
@@@ -/

def tiny : Rel Nat Nat := tinyMembershipPred

/- @@@
Now we're working across two levels of abstraction:
that of a binary relation, and that of the logical
predicate that specifies and represents it.

The tiny relation still acts just like a predicate.
We can apply it to a pair of arguments to produce a
membership proposition, the truth of which determines
whether the given pair of values is in relation or not.
It should be obvious that the membership proposition
is true for (tiny 1 1) and false for, e.g., (2, 2).
@@@ -/

#reduce (types := true) tiny 2 2
-- 2 = 0 ∧ 2 = 1 ∨ 2 = 1 ∧ 2 = 1 ∨ 2 = 1 ∧ 2 = 0

/- @@@
Relation-definitng predicates can defined using all
the various forms of logical expression: ∧, ∨, ¬, →,
↔, ∀, and ∃. Proving membership or not in an arbitrary
binary relation thus requires facility with proving
the full ranges of these types of proposition.
@@@ -/

/- @@@
## Proving Membership and Non-Membership Propositions

Now just as we proved set membership and non-membership
propositions by reducing these propositions to logical
propositions determined by the set membership predicate,
so now we do the same for binary relations.

Suppose we want to prove that (informally speaking) that
(0, 1) is in the tiny relation. We can start the proof by
saying this: *By the definition of tiny, what we are to
prove is 0 = 0 ∧ 1 = 1 ∨ 0 = 1 ∧ 1 = 1 ∨ 0 = 1 ∧ 1 = 0.
The remainder of the proof is then just an exercise in
*logical* proof construction, which you should now have
fully mastered.
@@@ -/

#reduce (types:=true) tiny 0 1

-- Prove (0, 1) is in tiny
example : tiny 0 1 :=
  /- @@@
  By the definition of tiny what is to be proved is
  0 = 0 ∧ 1 = 1 ∨ 0 = 1 ∧ 1 = 1 ∨ 0 = 1 ∧ 1 = 0. The
  proof is by *or introduction* on the left with ...
  @@@ -/
  Or.inl
    -- ... a proof of fst = 0 ∧ snd = 1
    (
      -- this proposition is proved by "and" introduction
      And.intro
        -- with a proof of 0 = 0 (parens needed here)
        (Eq.refl 0)
        -- and a proof of 1 = 1 (parens needed)
        (Eq.refl 1)
    )

/- @@@
Proving that a pair is not in a relation is done in the
usual way: by negation. That is, one assumes the pair is
in the relation and then shows that that cannot actually
be true, leading one to conclude that the negation of that
proposition is true. For example, let's show that (0, 0)
is not in the tiny relation.
@@@ -/

#reduce (types:=true) tiny 0 0
-- 0 = 0 ∧ 0 = 1 ∨ 0 = 1 ∧ 0 = 1 ∨ 0 = 1 ∧ 0 = 0


example : ¬tiny 0 0 :=
  -- The proof is by negation: we assume (0, 0) is in tiny ...
  fun (h : tiny 0 0) =>
    -- and show that this proof can't reallky exist
    -- the proof is by case analysis on h (Or.elim)
    match h with
    -- case (0, 0) = (0, 1)? I.e., 0 = 0 ∧ 0 = 1? Nope.
    -- by case analysis on a proof of 0 = 1 (no proofs)
    | Or.inl h01 => nomatch h01.right
    -- analyze the two remaining cases
    | Or.inr h11orh10 =>
      match h11orh10 with
      -- case (0, 0) = (1, 1)? I.e., 0 = 1 ∧ 0 = 1? Nope.
      | Or.inl h11 => nomatch h11.left
      -- case (0, 0) = (1, 0), i.e., 0 = 1 ∧ 0 = 0? Nope.
      | Or.inr h10 => nomatch h10.left

/- @@@
  As there can be no proof of (tiny 0 0), i.e., of
  0 = 0 ∧ 0 = 1 ∨ 0 = 1 ∧ 0 = 1 ∨ 0 = 1 ∧ 0 = 0, we
  conclude that (0, 0) is not in the tiny relation:
  ¬tiny 0 0. QED.

We now explore a range of particular relations to illustrate
concepts, specifications, propositions, and proofs involving
them. To avoid having to declare α and β as types and *r* as
a binary relation on them, we do it once here using the Lean
*variable* construct.
@@@ -/

variable
  (r : Rel α β)
  (a : α)
  (b : β)

#check r a b


/- @@@
## The Complete Binary Relation from α to β

Given sets (in type theory, types) α and β, the *complete*
relation from α to β relates every value of type α to every
value of type β.

The *complete* relation from α to β is "isomorphic" to the
*product* set/type, α × β, having every (a : α, b : β) pair
as a member. The corresponding membership predicate takes
two arguments, ignores them, and reduces to the membership
proposition, True. As there's always a proof of True, the
membership proposition is true for every pair of values,
so every pair of values is defined to be in the relation.
Here's a general definition of the complete relation on any
two types, α and β.
@@@ -/

def completeRel (α β : Type) : Rel α β := fun _ _ => True

/- @@@
This relation imposes no constraints on which String-Nat
pairs are in the relation, so they all are. The predicate
that defines this relation has to be true for *all* pairs
of values. The solution is for the predicate to yield the
proposition, True, for which there is always a proof, for
*any* pair of String and Nat values. In paper and pencil
set theoretic notation we could define fullStringNat as
{ (s,n ) | True }. In the type theory of Lean, specify the
relation using by defining its membership predicate.

As an example, we define completeStrNat as the complete
relation from String to Nat values. Be sure you see
what *completeRel String Nat* reduces to. What predicate
is it, exactly, as expressed formally in Lean. Do not
proceed if you're not sure, rather go back and figure
it out.
@@@ -/

def completeStrNat : Rel String Nat := completeRel String Nat

/- @@@
We can now apply this membership predicate to pairs of
argument values to yield *membership propositions* that
claim that such pairs are *in* the specified relation.
Here we claim that the pair, "Hello" and 2, is in this
relation. You *must* fully understand what proposition
*completeStrNat "Hello" 2* reduces do. *Go look at the
definition of completeStrNat if you're sure!*
@@@ -/

example : completeStrNat "Hello" 2 := True.intro

/- @@@
Given this definition we can show that any pair of values is in
the relation, or related to each other through or by it. As one
example, let's show that the pair of values, "Hello" and 7, is in
this relation. Hint. Start by *remembering* the definition of
completeStrNat, then start natural language proof by saying, "By
the definition of completeStrNat, what is to be proved is True."
Then prove that membership proposition.
@@@ -/

-- Prove ("Hello", 7) is in the complete relation on String and Nat
example : completeStrNat "Hello" 7 :=
  -- By the definition of completeStrNat, all we have to prove True
  -- The proof is by True introduction
  True.intro

-- Prove that *every* Nat-Nat pair is in completeStrNat
example : ∀ (a : String) (b : Nat), completeStrNat a b :=
fun a b => True.intro

/- @@@
To know to "unfold" definitions into their underlying
definitions is an incredibly important and useful move
in in proof construction. I'd recommend that if you're
ever stuck proving a proposition, just look to see if
you can unfold any definitions to reveal more clearly
what actually needs to be proved. Sometimes even Lean
will get stuck computing proofs automatically until you
tell it to unfold a definition in the midst of a proof
construction.
@@@ -/

/- @@@
## The Empty Binary Relation From α to β

The empty relation from any type/set α to and type/set β
is the relation that relates no values of α to any values
of β. It's the relation that contains no pairs.

We specify the empty on α and β with a membership predicate
that is false for any pair of values. It's a predicate that
ignores its arguments and yields the membership proposition,
False. No pair satisfies this membership proposition (makes
it true), so the specified relation has no pairs at all.
@@@ -/

def emptyRel {α β : Type*} : Rel α β := fun _ _ => False

/- @@@
The domain of definition of the empty relation is still
the set of all values of type α, and the co-domain is
still the set of all β values; but the domain and range
are both empty, because the set of pairs of r is empty.
@@@ -/

/- @@@
Let's now see some example. First we claim and show that no
pair, (a : α, b : β) can be in an empty relation. We should
be able to state and prove this proposition formally. Recall
that we've already defined (a : α) and (b : β) as arbitrary
values. The proof is by negation.

We assume(emptyRel a b) is true with a proof, h. But by
the definition of emptyRel, the membership proposition,
(emptyRel a b), is the proposition False. This makes h
a proof of False, which is what we need to conclude our
proof of ¬(emptyRel a b). QED.
@@@ -/
example (a : α) (b : β) : ¬emptyRel a b :=
fun h => h

/- @@@
As a minor note, if we handn't already assumed that a
and b are arbitrary objects, we could introduce them as
such using ∀. You can read this proposition as something
to the effect, no pair of objects, (a, b), can belong to
and empty relation on any α and β.
@@@ -/

example : ∀ {α β : Type*}, ∀ (a : α), ∀ (b : β), ¬emptyRel a b :=
/- @@@
Proof by ∀ introduction. We assume arbitrary and and b and
then show that this pair cannot be in an empty relation. The
rest of the proof is by negation. We assume (h : emptyRel a b)
and produce a proof of False. By the definition of emptyRel,
(h : emptyRel x y) *is* a proof of False. Therefore, we can
conclude that ¬(emptyRel x y).
@@@ -/
fun a b =>     -- assume arbitrary a and b (can use _'s here)
  fun h =>     -- assume a proof of (emptyRel a b), call it h
    h          -- It *is* a proof of False, thus ¬emptyRel a b.


/- @@@
Next we claim and prove the claim that no pair can Be in
the empty relation from String to Nat, in particular.

The empty relation on String and Nat is just the polymorphic
(with type arguments) empty relation specialized to the
types, α = String and β = Nat. EmptyRel does take two Type
arguments, but they are defined to be implicit: Lean infers
them from the type of emptyStrNat, namely *Rel String Nat*.
@@@ -/

def emptyStrNat : Rel String Nat := emptyRel

/- @@@
In the following proof by negation, we assume we have
a proof, *h* of the proposition that the pair, s and n,
is in the relation and we need a proof of False. Study
this example until you see with absolute clarity that
*h* is assumed to be exactly that. Go back and study the
definition of emptyStrNat if you're not sure why!
@@@ -/

example : ∀ s n, ¬emptyStrNat s n := fun s n h => h

/- @@@
## Relations Neither Empty or Complete
The empty and complete relation aren't very informative.
The interesting ones are proper but non-empty subsets of
the complete relation on their argument types. Let's see
examples of some more interesting, less trivial, relations.

As an example, consider the "subrelation" of our full
String to Nat relation with a pair *(s, n)*, is in the
relation if and only if *n is equal to the length of s*.
In Lean, the *String.length* function takes a string and
returns its length. We can use it to specify the relation
we want, as follows.
@@@ -/

def strlen : Rel String Nat := fun s n => n = s.length

/- @@@
We want to take a moment at this point to note a critical
distinction between *relations* in Lean and functions that
are represented as lambda expressions (ordinary computable
functions in Lean). Functions in Lean and related systems
are (1) computable, and (2) complete, which is to say for *any*
value of the declared input type a function must return some
value of the output type.

By contrast, relations in Lean need not be compelte. We have
already seen an example in  (with a defined output for every
input); and they can be multi-valued, with several outputs for
any given input.

Concerning completeness, a quick look back at the empty relation
makes the point: the domain of definition is every value, but
the relation has no pairs: it does not define an output for
any of them. As far as being multi-valued, consider the complete
relation defined about. It defines *every* value of the output
type as an output for each and every value of the input type.

Finally, consider computability. We could easily define a
computable function that *computes* to our strlen relation.
@@@ -/

def strlenFun : String → Nat := fun s => s.length
#reduce strlenFun "Hello"   -- computes 5

/- @@@
However, our strlen relation is not a computable function,
but rather a *declarative specification*. When you apply
it to values of its input types, you get not the output of
the relation for those value, but a proposition that might
or might not have a proof. If there is a proof (which you
have to confirm yourself), you have a member; otherwise no.

In a nutshell, if you need to specify a *partial function*
in Lean, or a multi-valued relation, then you have to do it
with a declarative specification, not a computable function.
@@@ -/

/- @@@
Here's yet another example. While we were able to prove
that ("Hello", 7) is in the complete relation from String to
Nat, there is no proof that this pair is in strlen, which has
a much more restrictive membership predicate. Simply put, the
length of "Hello" (defined in the Lean libraries), is 5, and
7 is not equal to 5, so this pair can't be a member.
@@@ -/

example : strlen "Hello" 7 :=
-- What we need to prove is 7 = "Hello".length, i.e., 7 = 5.
  _     -- We're stuck, as there can be no proof of that.


/- @@@
We can of course prove that ("Hello", 7) is *not* in the
strlen relation. The proof is by negation. We'lll assume
this pair is the relation. That'll lead to the assumption
that 7 = 5, which is absurd. From that contradiction, we'll
conclude that the pair is *not* in the strlen relation.
@@@ -/

example : ¬strlen "Hello" 7 :=

/- @@@
The proof is constructed by negation. Assume strlen "Hello" 7;
show that leads to a contradiction; conclude ¬strlen "Hello" 7.
You must know this concept, be able to state it clearly, be able
to see when you need it; and be able to use in to construct proofs
whether formal or informal. So here we go. (1) By the definition
of ¬, what we are really to prove is (strlen "Hello" 7) → False.
This is an implication. To prove it we will assume the premise is
true and that we have a proof of it (h : strlen "Hello" 7), and
we will then show that that can't happen (as revealed by the fact
that we'll have created a contradiction, showing that the initial
assumption was wrong).
@@@ -/
fun (h : strlen "Hello" 7) =>
/- @@@
Now that we have our assumed proof of (strlen "Hello" 7) we have
to show that there's a contraction from which we can derive a
proof of False. The only information we have is the proof, h.
But how can we use it? The answer, for you, is that you again
want to see the need to expand a definition, here of the term,
(strlen "Hello" 7). What does that mean? *Go back and study the
definition of strlen!* It means (7 = "Hello".length), which is
to say, it means (7 = 5), as Lean will "run" the length function
to reduce "Hello".length to the result, 5. There can be no proof
of 7 = 5, because the only constructor of equality proofs, Eq.refl,
can only construct proofs that objects are equal to themselves.

Another way to say this is that we'll show that we can have a
proof of false for every possible proof, h, of 7 = 5; but there
are no, so showing that False is true in all cases is trivial,
as there is no case that can possibly account for h.
@@@ -/
  nomatch h

/- @@@
As a final example, we can prove that the pair, ("Hello",5), is
in strlen. In English, all we'd have to say is that this pair
satisfies the membership predicate because 5 = "Hello".length
(assuming we've properly defined "length,." which Lean has. )
@@@ -/

example : strlen "Hello" 5 :=
/- @@@
By the definition of strlen, we must prove 5 = "Hello".length.
By the computation/reduction of "Hello".length this means 5 = 5.
And that is true by the reflecxivity of equality, as for any
value, k, whatsoever, we can have a proof of k = k by the rule
of equality introduction, Eq.refl k. The "rfl" construct we've
used in the past is just a shorthand for that, defined to infer
the value of k from context. And Lean takes care of reducing the
length function for us. We could write rfl here, but let's use
(Eq.refl 5) to get a better visual of the idea that what we're
producing here is a proof of 5 = 5.
@@@ -/
Eq.refl 5


/- @@@
## Finite Relations

A finite binary relation is a binary relation having only a
finite set of pairs. For example, let's specify a String-to-Nat
relation with just three String-Nat pairsW. e'll call strlen3,
and will define it as (essentially) with the following three
pairs:

def strlen3 :=
  {
    ("Hello", 5),
    ("Lean",  4),
    ("!",     1)
  }

To specify this relation formally in Lean all we have to do
is to figure out how to write the membership predicate. In
this example, we'll do it as a three-clause disjunction, one
clause for each pair.
@@@ -/

def strlen3 : Rel String Nat :=
  fun s n =>
    (s = "Hello" ∧ n = 5) ∨
    (s = "Lean" ∧ n = 4) ∨
    (s = "!" ∧ n = 1)

/- @@@
We can prove memberships and non-membership of pairs in this
relation in the usual way: by proving the proposition that is
the result of applying the membership predicate to any pair of
values. Here such a proposition will be a disjunction. Again
you must be able to reduce a relation membership proposition,
such as *strlen3 "Hello" 5* to its underlying logical form.
If you're not sure, you can use #reduce (types := true).
@@@ -/

#reduce (types := true) strlen3 "Hello" 5

/- @@@
We see *by the definition* of strlen3, it will suffice to show
that "Hello" = "Hello" ∧ 5 = 5 ∨ "Hello" = "Lean" ∧ 5 = 4 ∨
"Hello" = "!" ∧ 5 = 1. Copy of the body of *strlen3* and for
the formal parameters, substitute in the actual parameters. The
result is the membership proposition for those parameter values.
Here's what it looks like to prove this proposition.
@@@ -/

example : strlen3 "Hello" 5 :=
  -- we prove the result of applying strlen3 to "Hello" and 5:
  -- ("Hello" = "Hello" ∧ 5 = 5) ∨ ("Hello" = "Lean" ∧ 5 = 4) ∨ ("Hello" = "!" ∧ 5 = 1)
  -- We can prove (and can only prove) the left disjunct; then it's two equalities
  Or.inl    -- prove the left disjunct ("Hello" = "Hello" ∧ 5 = 5), using Or.intro
    (
      And.intro   -- proof by and introduction
      rfl         -- "Hello" = "Hello"
      rfl         -- 5 = 5
    )

/- @@@
We can also prove that ("Hello", 4) is not in the relation.
The proof is by negation followed by case analysis on the
3-case disjunction that defines the membership predicate.
We will assume (strlen3 "Hello" 4) is in the relation and t
then show that it doesn't satisfy any of the three disjuncts
and so can't be. From this contradiction we'll conclude that
¬(strlen3 "Hello" 4) is true.
@@@ -/

example : ¬strlen3 "Hello" 4 := fun h =>
-- proof by case analysis on assumed proof h : (strlen3 "Hello" 4),
-- which is to say h is a proof of ("Hello" = "Hello" ∧ 4 = 5) ∨ ...
match h with
  -- Is ("Hello", 4) the first allow pair, ("Hello", 5)?
  | Or.inl (p1 : "Hello" = "Hello" ∧ 4 = 5) =>
      let f : 4 = 5 := p1.right
      nomatch f       -- nope, can't have a proof of 4 = 5
  -- case analysis on right side of disjunction
  | Or.inr (rest : "Hello" = "Lean" ∧ 4 = 4 ∨ "Hello" = "!" ∧ 4 = 1) =>
      match rest with
      -- Is ("Hello", 4) the second allowed pair, ("Lean", 4)?
      | Or.inl p2 =>
        let f : "Hello" = "Lean" := p2.left
        nomatch f       -- nope, can't have proof of "Hello" = "Lean"
        -- Is ("Hello", 4) the third and last allowed pair, ("!", 1)
      | Or.inr p3 =>
        let f : "Hello" = "!" := p3.left
        nomatch f         -- nope, can't haver a proof of "Hello" = "!"
/- @@@
Having shown there can be no proof of strlen3 "Hello" 4,
we conclude ¬strlen3 "Hello" 4. QED.
@@@ -/

-- Lean's smart enough to do all that work for us
example : ¬strlen "Hello" 4 := fun h => nomatch h


/- @@@
## Elements of a Binary Relation
In this section, we define important terms and underlying
concepts in the theory of relations. To illustrate the ideas,
we'll refer back to our running examples.
@@@ -/

/- @@@

### Domain of Definition and Co-Domain

Given any relation, $r$ on sets of types, *α* and *β*,
the *domain of definition* of *r* *(r.dom)* is the set,
given by a type in Lean, from which all possible inputs
to *r* (left elements pairs) are drawn. The co-domain is
the set, in Lean the type, of all possible output values
(right elements of pairs).

We will speak in type theoretical terms, and thus have
specified the domain of definition and co-domain sets as
types. This is nice as Lean can now typecheck values to
see if they're in these sets.

Now we can specify any binary relation from α (input side)
to β (output side) values, as a *predicate, p, on *α* and
*β*, thus being of type *(p : α → β → Prop)*. Lean, as we
have seen, provides the polymorphic type, *Rel α β* as an
abstraction from *α → β → Prop*, used particularly when a
predicate is representing a binary relation, in particular.

With that representation, we can now see how we can return
the *domain of definition* of *r*, as the sets of all values
(the *universals* sets) of types, α, and β, respectively.
@@@ -/

def domDef (r : Rel α β) : Set α := Set.univ
def codom (r : Rel α β) : Set β := Set.univ

/- @@@
Let's see some applications.
@@@ -/

-- The domain of definition of strlen3 is a set of strings
-- The codomain of strlen3 is a set atural numbers

#check (domDef strlen3)
#check (codom strlen3)

-- Its domain of definition is the set of all strings
-- Its codomain is the set of all natural numbers

#reduce (domDef strlen3)
#reduce (codom strlen3)



/- @@@
### Domain and Range of a Binary Relation on α and β

We now define what it means for a set to be, respectively,
the *domain* or the *range* of *r*. The *domain* of *r* is
the set of all *(a : α)* values for which *r* there is some
corresponding β value, *b*, such that the pair *(a, b)* is
in the relation *r*. Similarly, the *range* of *r* is the
set of all output values, *(b : β)* for which there is some
input value, *(a : α),* where *r* relates *a* and *b*.
@@@ -/

def dom (r : Rel α β) : Set α := { a | ∃ b, r a b }
def ran (r : Rel α β) : Set β := { b | ∃ a, r a b }

-- Let's look at some applications


-- set types
#check dom strlen3    -- a set of strings
#check ran strlen3    -- a set of natural numbers

-- set values
#reduce dom strlen3   -- fun a => ∃ b, strlen3 a b
#reduce ran strlen3   -- fun b => ∃ a, strlen3 a b


-- /- @@@
-- The domain of definition and the codomain of each of the relations
-- we've specified as examples are all values of type α = String and
-- all values of type β = Nat, respectively.

-- The set of values, (a : α), that r *does* relate to β values,
-- i.e., the set of values that do appear in the first position of
-- any ordered pair, (a : α, b : β) in r, is called the *domain*
-- of r. The domain of r is the set of values on which r is said
-- to be *defined*. It's the set of *input* values, (a : α), for
-- which r specifies at least one output value, (b : β).

-- More formally, given a relation, r : Rel α β, the domain of r is
-- defined to be the set { x : α | ∃ y : β, r x y }. Another way to
-- say this is that the domain of r is the set of α values specified
-- by the predicate, fun x => ∃ y, r x y. In other words, x : α is
-- in  the domain of r if any only if there's some y : β such that
-- the pair of values, x, y, satisfies the two-place predicate r.

-- In Lean, if r is a binary relation (Rel.dom r) is its domain set.
-- We can define the domain of definition and the domain of any binary
-- relation as follows.
-- @@@ -/

-- def dom (r : Rel α β) : Set α := { a | ∃ b, r a b }
-- def domDef (r : Rel α β) : Type := α

-- /- @@@
-- The *domain of definition* of a relation is thus the set of
-- possible input values, that can appear as first arguments in
-- membership propostions. The *domain* of a relation is the subset
-- of its domain of definition for which there are corresponding
-- output values. The codomain is the set of values (type in Lean)
-- containing all possible output values. The range of a relation
-- is the subset of values in the codomaim for which there really
-- are corresonding related input values in the domain.
-- @@@ -/

-- def codom (r : Rel α β) : Type := β
-- def ran (r : Rel α β) : Set β := { b | ∃ a, r a b }

/- @@@
### Lean's Definitions

We didn's have to define these operations ourselves, as Lean
provides them to us from its libraries. In particular, *Rel.dom*
reduces to the domain of any relation, and Rel.codom *sadly*
reduces to its range as we've defined these terms here.
@@@ --/

#reduce (types := true) Rel.dom r
-- fun x => ∃ y, r x y

#reduce (types := true) Rel.codom r
-- fun y => ∃ x, r x y

-- /- @@@
-- Regrettably, Lean defines *codom* to be what we have called
-- the *range* of a relation.
-- As I said in class, these terms are used somewhat inconcistenty
-- in the mathematics literature. For this class we'll stick with
-- the *concepts* as we've defined them here, with the *range* of a
-- relation being the set of all output values for which there is
-- a corresponding input.
-- @@@ -/


/- @@@
### More Examples

We'll start by looking at the domains of a few of the relations
we've already introduced.
@@@ -/

#reduce Rel.dom strlen
-- fun x => ∃ y, strlen x y
-- think of this as the set  { x | ∃ y, strlen x y}

#reduce Rel.dom emptyStrNat
-- fun x => ∃ y, emptyStrNat x y
-- think of this as { x | ∃ y, emptyStrNat x y }
-- equivalently { x | ∃ y, False }

/- @@@
We can now prove, for example, that "Hello" ∈ strlen3.dom.
By the definition of the domain of a relation, we need to
show (∃ y, strlen3 "Hello" y). As a witness for y, 5 will do.
@@@ -/

#reduce (types := true) ("Hello" ∈ strlen3.dom )

example : "Hello" ∈ strlen3.dom :=
  -- Prove there is (exist) some y such that ("Hello", y) is in strlen3.
  -- A constructive proof requires a witness for y. Clearly y = 5 will work
  Exists.intro                    -- Apply the inference rule
    5                             -- to y = 5 as a witness
    (Or.inl (And.intro rfl rfl))  -- with a proof that ("Hello", y=5) in is strlen3


-- Here's the definition of the range (called *codom*)
#reduce strlen3.codom

-- Here's the definition of the range of strlen3
#reduce (types:=true) strlen3.codom
-- fun y => ∃ x, strlen3 x y

/- @@@
With all of that, it should be clear that we can
express propositions about certain values being in
or not in the domain or range of a relation, and
then try to prove them by reducing the definitions
of these terms to their logical meanings. Let's try
to prove that 5 is in the codomain of strlen3, for
example.

In a natural language informal proof, we could
start by saying, "By the definitions of strlen
and range (codom), what remains to be proved is"
```lean
∃ x,  x = "Hello" ∧ 5 = 5 ∨
      x = "Lean" ∧ 5 = 4  ∨
      x = "!" ∧ 5 = 1
```

The initial step is thus to apply the introduction
rule for exists. And the rest is just basic logic.
@@@ -/

#reduce (types := true) 5 ∈ strlen3.codom

example : 5 ∈ strlen3.codom :=
Exists.intro
  "Hello"                 -- Use "Hello" as a witness
  (Or.inl                 -- Now a proof that it works
    (And.intro rfl rfl)
  )


/- @@@
## The Inverse of a Binary Relation on Types/Sets α and β

The inverse of a relation, r, on α and β, is a relation on
β and α, comprising all the pair from r but with the first
and second element values swapped. Sometimes you'll see the
inverse of a binary relation, r, written as r⁻¹.
@@@ -/

#reduce Rel.inv
/- @@@
The specification is easy. The membership predicate for
a pair, (b, a), to be in the inverse of a relation r is
that the pair (a, b) is in r. Think about it and you will
see that r.inv has to be the same as r but with all pairs
flipped.
@@@ -/

def inv (r : Rel α β) : Rel β α := fun b a => r a b

/- @@@
Example: What is the inverse of strlen3? In Lean it's writen
either (Rel.inv strlen3) or just strlen.inv. Remeber, This is
a predicate being used to represent a relation. The inverse
of r is a new predicate. If r takes areguments, a of types α,
and then b of type β, then r.inv takes as arguments some
(b : β) and (a : α) and returns the proposition that (a, b)
is in r. If there's a proof of that, then (b, a) is specified
to be in r.inv. To so prove that some (b, a) is in r⁻¹, you
just show that (a, b) ∈ r.
@@@ -/

/- @@@
Conjecture: (5, "Hello") is in the inverse of strlen3.
Proof: it suffices to prove ("Hello", 5) is in r. But
we've already done that once and don need to do it again
here! Oh, well, ok.
@@@ -/

#reduce (types := true) strlen3.inv 5 "Hello"

example : strlen3.inv 5 "Hello"
  :=
/- @@@
  By the definition of the inverse of a relation,
  the proposition, (strlen3.inv 5 "Hello"), which
  we are to prove, reduces to (strlen3 "Hello" 5).
  By the definition of strlen3, this proposition
  tne reduces to ("Hello" = "Hello" ∧ 5 = 5) ∨ ...
  This proposition is now proved by or introduction
  on the left.
@@@ -/
  Or.inl ⟨ rfl, rfl⟩
-- Remember ⟨ _, _ ⟩ here is shorthand for And.intro

/- @@@
We can actually now state and prove more general theorems
showing that the inverse operation has the property that
appying it twice is equivalent to doing nothing at all.
Think about it: if (a, b) is in r, then (b, a) is in the
inverse of r, but now (a, b) must be in the inverse  of
this inverse of r. Going the other way, if (a, b) is in
the inverse of the inverse of r, then (b, a) must be in
the inverse of r, in whcih case (a, b) must be in r. In
other words, (a, b) is in r if and only if (a, b) is in
the inverse of the inverse of r. We want to know that this
statement is true for *any* values of a and b (of their
respective types).
@@@ -/

theorem inverseInverseIsId:
  ∀ {α β : Type} (rel : Rel α β) (a : α) (b : β), rel a b ↔ rel.inv.inv a b :=
-- assume a and b are arbitrary values (by ∀ introduction)
fun rel a b =>
-- prove r a b ↔ r.inv.inv a b
-- by iff intro on proofs of the two implications
Iff.intro
  -- prove r a b → r.inv.inv a b
  (
    -- assume h : r a b
    -- show r.inv.inv a b
    -- but h already proves it
    -- because r.inv.inv is r
    fun h : rel a b => h
  )
  (
    -- assume h : r.inv.inv a b
    -- show r a b
    -- but h already proves it
    -- because r is r.inv.inv
    fun h : rel a b => h
  )

/- @@@
## The Image of a Set Under a Binary Relation

Suppose we have a binary relation, (r : Rel α β),
and a set of α values, (s : Set α). The image of s
under r is the set of values that, in a sense, you
get by iterating over all the elements of s, getting
one element, e, at a time, then finding all the the
"output" values in r for that one "input" value and
finally combinining all of these output into  output
set. We don't write that as a program, though, but
as a mathematical specification.

Here you can see the formal definition of the image
of a set s under a relation r.
@@@ -/

#reduce Rel.image
-- fun r s y => ∃ x ∈ s, r x y

/- @@@
Given a relation, r, a set of input values, s, and a
y of the output type, y is specified to be in the image
of r when there is some input value, x, in s, such that
r relates x to y. In other words, the image of s under r
is the set of all output values for any and all ainput
values in s.
@@@ -/

#reduce Rel.image
-- fun r s y => ∃ x ∈ s, r x y
/- @@@
Given any relation, r, and any set of input values,
s, an output value y is (defined to be) in "the image
of s under r" exactly when y is the output of r for
at least one (some) value x in the set s. The image
operator on a relation acts like it's applying the
whole relation to a whole set of values and getting
back all values related to any value in the argument
set.
@@@ -/

/- @@@
In this example we consider the image of the two-member
set, { "Hello", "!"}, under the strlen3 relation. You can
see intuitively that it must be the set {5, 1}, insofar as
strlen3 relates "Hello" to (only) 5, and "!" to (only) and
there are no other values in s. Let's see what we're saying
formally, as reported by Lean. *Be sure you understand all
of the outputs of #reduce that we're presenting over in this
lesson!
@@@ -/

#reduce Rel.image strlen3 { "Hello", "!"}
-- Here's an easier way to write the same thing
#reduce strlen3.image {"Hello", "!"}
-- fun y => ∃ x ∈ {"Hello", "!"}, strlen3 x y

/- @@@
The image, specified by the *single-argument* predicate,
fun y => ∃ x ∈ {"Hello", "!"}, strlen3 x y, is, again, the
set of all output (β) values, y, such that, for any given y
there is some x in s that r relates to y.
@@@ -/

/- @@@
Given this definition and our understanding, we see that
it should be possible to show that, say, 1, is in the
image of { "Hello", "!"} under strlen3, because there is
a string in the set,  { "Hello", "!"}, namely "!", that
r relates to 1 (for which (strlen3 "!" 1) is true).
@@@ -/

example : 1 ∈ strlen3.image { "Hello", "!"} :=
/- @@@
By the definition of Rel.image we need to prove
is that there is some string, x, in the set, call
it s, of strings, that satisfies strlen3 s 1. This
string, in s, will of course be "!", so that will
be our witness. The proof is by exits introduction
with "!" as the witness.
@@@ -/
Exists.intro "!"
(
  -- what remains to be proved is "!" ∈ {"Hello", "!"} ∧ strlen3 "!" 1
  -- the proof is by and introduction
  And.intro

     -- prove: "!" ∈ {"Hello", "!"}
     -- this is obvious but, sorry, maybe I'll prove it later
    (sorry)

    -- prove: strlen3 "!" 1
    -- this is obvious but, sorry, maybe I'll prove it later
    (sorry)
)

/- @@@
We should also be able to show that 4 is not in the image of
s under strlen3. The proof is by negation. We'll assume that
4 is in the image, but we have already figured out that the
only elements in there are 5 and 1 (from "Hello" and "!"). The
problem will be that assuming 4 is in the set isto assume that
4 = 5 ∨ 4 = 1. That's a contraction as each case leads to an
impossibiility. Thus 4 ∉ strlen3.image { "Hello", "!"}. QED,
@@@ -/

example : 4 ∉ strlen3.image { "Hello", "!"}  :=
-- assume, h, that 4 is in this set
fun h =>
  -- From 4 ∈ strlen3.image {"Hello", "!"}, prove False
  -- By the definition of image, h proves ∃ s, strlen3 s 4
  -- The only information we have to work with is h
  -- And the only thing we can do with it is elimination
  Exists.elim
    h
    -- ∀ (a : String), a ∈ {"Hello", "!"} ∧ strlen3 a 4 → False
    -- we assumed r relates some string in s to 4 call it w
    (
      fun w =>
        (
          -- prove: w ∈ {"Hello", "!"} ∧ strlen3 w 4 → False
          -- assume premise : w ∈ {"Hello", "!"} ∧ strlen3 w 4
          fun p =>
          (
            let l := p.left
            -- TODO
            let r := p.right

            -- recognize that w proves a disjunction
            -- eliminate using Or.elim via pattern matching
            -- case analysis
            match l with
            -- left case, with "hello" a proof of w = "Hello" (in this case)
            -- we also have r, a proof of (strlen3 w 4)
            -- we can use "hello" to rewrite (strlen3 w 4) to (strlen3 "Hello" 4)
            -- by the definition of strlen3 this is a disjuncion that is false
            -- using
            | Or.inl hello =>
              /- @@@
                We haven't talked about "tactic mode" in Lean. Without getting
                into details, we're arging that because "hello" proves w = "Hello",
                we can replace w in r, which proves strlen3 w 4, to get a proof
                of strlen3 "Hello" 4. But the pair, ("Hello", 4), is not in the
                strlen3 relation, as that pair of arguments doesn't satisfy the
                constraint it imposes on membership. The nomatch construct does
                a case analysis on this rewritten version of r and finding that
                there are no ways it could be true, dismisses this overall case.
              @@@ -/
              (
                by
                  rw [hello] at r
                  nomatch r
              )

            -- the second case, w ∈ { "!" } requires deducing from that that w = "!"
            -- that then allows us to rewrite (strlen3 w 4) to (strlen3 "!" 4)
            -- by the definition of strlen3, that'd mean, inter alia, that 1 = 4
            | Or.inr excl  =>
              (
                have wexcl : w = "!" := excl
                (
                  by
                    rw [wexcl] at r
                    nomatch r
                )
              )
          )
        )
    )

/- @@@
In each case, where s = "Hello" or where s = "!", we have a
contradiction: that s.length (either 5 or 1) is equal to 4.
In each case we're able to derive a contradiction, showing
that the assumption that 4 ∈ strlen3.image {"Hello", "!"} is
wrong, therefore ¬4 ∈ strlen3.image {"Hello", "!"} is true.
QED.
@@@ -/

/- @@@
## The Preimage of a Set under a Relation

Given a relation, *r*, the pre-image of a set, *t*, of values
from the codomain, is the set, s, of values from the domain that
have related values in *t*.
@@@ -/

#reduce Rel.preimage
-- fun r s y => ∃ x ∈ s, r.inv x y

/- @@@
Example: Mary's Bank Account Numbers

Let's make up a new example. We want to create
a little "relational database" with one relation,
a binary relation, that associates each person
(ok, their name as a string) with his or her bank
account number(s), if any.

There's no limit on the number of bank accounts
any single person can have. A person could have
no bank accounts, as well. To be concrete, let's
assume there are three people, "Mary," "Lu," and
"Bob", that Mary has accounts #1 and #2; Lu has
account #3; and that Bob has no bank account at all.

We can think of the relation (call it acctsOf) as
the set of pairs, { Mary, 1), (Mary, 2), (Lu, 3) }.
One thing to see here is that the image of { Mary }
under acctsOf is not a single value but a set of two
values: {1, 2}. This relation is not single-valued.
Another point is that it's not complete, as there
is no output at all for Bob.
@@@ -/

def acctsOf : Rel String Nat := fun s n =>
s = "Mary" ∧ n = 1 ∨
s = "Mary" ∧ n = 2 ∨
s = "Lu"   ∧ n = 3

/- @@@
Let's remind ourselves how the image of the set,
{ "Mary" } under the acctsOf relation is defined.
As usual, hover over "#reduce" to see its output.
It's the set of output numbers related to any of
the values in the set *{ "Mary"}*, represented as
a predicate.
@@@ -/

#reduce acctsOf.image { "Mary" }

/- @@@
So, *acctsOf.image {"Mary"}* is the set of output
values, represented by the predicate, *fun y => ∃ x ∈ {"Mary"},
acctsOf x y.* In English, this is the set of output numbers, *y*
for which there are related people in the input set, *{ "Mary" }*.

With that, we can now write propositions about membership
of numbers in such an *image* set.
@@@ -/

-- Proof that 1 is in acctsOf.image { "Mary" }
example : 1 ∈ acctsOf.image { "Mary" } :=
/- @@@
By the definition of image, we need to prove
∃ x ∈ {"Mary"}, acctsOf x y. At this point, we
have to find/pick a witness---here an input value
in the set, { "Mary"} )--- for which 1 is among
the outputs. Then we just prove that that pair
is in fact in the relation.

The proof is by exists introduction. We show
that there is some x in { "Mary" } *and* for
that x, (x, 1) is in acctsOf. The only possible
x to choose in this case is "Mary".
@@@ -/

-- Pick "Mary" as the witness
(Exists.intro "Mary"
  -- now prove "Mary" ∈ { "Mary" } ∧ acctsOf "Mary" 1
  -- the proof if of course by and introduction
  (And.intro
    -- Exercise: prove "Mary" ∈ { "Mary" }
    (sorry)
    -- Exercise: prove (acctsOf "Mary" 1)
    (sorry)
  )
)

-- Exercise: Prove that 2 is also in the image of { "Mary"}
example : 2 ∈ acctsOf.image { "Mary" } := _

-- Exercise: Prove that 3 is NOT one of Mary's bank accounts
-- HERE:


/- @@@
## A Most Fundamental Relation: Equality

The Equality Relation in Lean, called *Eq* is defined as an
inductive type whose values are proofs of equalities between
terms *up to reduction*. The *=* symbol is an infix notation
for *Eq*, so instead of writing *Eq a b* we can write *a = b*.

Such an equality proposition has a proof if and only if both
sides *reduce* to the same term. For example, *1 + 1 = 2* has
a proof because *1 + 1* reduces to *2*, leaving only *2 = 2*
to be proved. The single proof constructor for *Eq*, called
*Eq.refl,* takes any value of any type, (a : α) and constructs
a proof of *a = a*. Applying it to *2* thus yields a proof of
*2 = 2*, and that's what we wanted to confirm.
@@@ -/

example : 1 + 1 = 2 := rfl

/- @@@
Here's the definition of the equality type in Lean.
@@@ -/

#check Eq     -- right click and go to definition

/- @@@
```lean
inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a
```

The first line establishes that *Eq* takes two arguments,
*a* and *b*, and yields the proposition, *Eq a b,* which
with infix notation is usually written *a = b*. The second
line provides the sole means of proving an equality. It
takes *1* argument, *a*, and return a proof that *a = a*.
@@@ -/

example : 1 + 1 = 2 := Eq.refl 2

/- @@@
So what about rfl? Here's how it's defined.

```lean
 rfl {α : Sort u} {a : α} : Eq a a := Eq.refl a
```

It's special power is that it infers both *α* and
*a* and returns a proof of *a = a* by reducing to
*Eq.refl a*. It works so long as Lean can infer both
values. If not, then use *Eq.refl a*.
@@@-/


/- @@@
## Example: The Unit Circle in the Cartesian Plane

The unit circle in the Cartesian plane is the set of points,
represented by ordered pairs of real numbers, *(x, y)*, that
satsify the predicate, x² + y² = 1. The points *(0, 1)* and
*(0,1)* are on the circle, but *(0,0)* isn't, as *0² + 1² = 1*
but *0² + 0² ≠ 1*.

Now we can give a formal definition of the relation. See the
import at the top of this file for the Real numbers. In Lean,
*Real* is the type of the real numbers. With that, here's the
definition. Note that just as we can use ℕ for Nat, so we can
use ℝ for Real, mirroring the use of these *blackboard font*
notations by most mathematicians.
@@@ -/

def unitCircle : Rel ℝ ℝ := fun x y => x^2 + y^2 = 1

/- @@@
So now let's state and try to prove the proposition that
the pair, *(0, 1)* is in this relation (on the unit circle).
Here's the proposition itself.
@@@ -/

def zoUnitCircle : Prop := unitCircle 0 1

/- @@@
We might expect that by the definition of *unitCircle*
this proposition would reduce to *0² + 1² = 1*, with the
expression *0² + 1²* then reducing to *1 = 1*, with *rfl*
as an easy proof.
@@@ -/

example : unitCircle 0 (-1) := rfl    -- doesn't work!

/- @@@
That didn't work! The problem is that the real numbers
*are not computable* (!) so Lean cannot reduce *0² + 1²*
to *1* computationally. Instead, opne must must *reason*
logically reals based on the axioms used to define them
and theorems already proved from those axioms. One must
*deduce* that *0² + 1²*.

You can do such reasoning entirely on your own, but it is
tedious and requires an understanding of definitions and
previously proved theorems about real numbers.

The good news is that Lean provides a vast library of programs
that *automate* aspects of proof construction. These programs,
themselves written in Lean, take the current proof state, goal,
and other inputs and try to prove the goal. These programs are
called *tactics*. To finish off this chapter, we will take the
opportunity to give a first taste of tactic-based proving, for
the particular problem we face right here.
@@@ -/

/- @@@
## Tactics: Automating Steps in Proof Construction

A tactic is not a proof term, but rather a program, that
someone wrote, in Lean, that *attempt* to construct a proof
term for the current goal. These terms usually have remaining
*holes* to be filled in, which become the new *goals* to be
proved.

### The simp Automates Reasoning to Simplify Expressions

One of the most widely used tactics in Lean is called *simp*.
It has a default database of already accepted definitions, e.g.,
of functions, theorems, etc., and tries to find a way to apply
them to simplify a goal so that you don't have to do by hand,

In the best cases, it will simplify a goal to an equality that
can finally be proven by Eq.refl or rfl, which the tactic will
apply for you. As an example, here is how we can use the *simp*
tactic to obtain a proof term that shows that *(0, -1) = 1* in
the real numbers, and is thus on the unit circle.
@@@ -/

theorem zeroMinusOneOnUnitCircle : unitCircle 0 (-1) :=
by
  simp [unitCircle]

/- @@@
The keyword, *by*, places Lean in *tactic mode*. It
is in this mode that you can run tactics. In general
you can mix *term* and *tactic* modes in constructing
proofs in Lean. We will see more of tactics later on.

Here we run *simp*, informing it of the definition
of the definition of *unitCircle*. This tactic will
then combine this definition with other dedinitions
in its database, to try to prove the goal. Here, the
tactic succeeds in producing a proof term that Lean
then checks and accepts.

Tactics do not always succeed. In that case you will
get an error message and your proof state (sequent) will
be unchanged. Moreover, even if a mistake was made in the
implementation of a tactic, Lean still checks the proof
terms it produces, just as if you had produced them by hand.
Tactics are thus not of the correctness-critical part of
Lean, and even if buggy tactics succeed in producing bad
proof terms, Lean will still check, and not accept, them.

You don't ordinarily see the *proof terms*  that tactics
construct. You can nevertheless now have confidence that
*(0, -1)* is on the unit circle in the Cartesian plan, as
Lean has checked and accepted the generated proof term.

The translation into English of the tactic-built proof that
*simp* finds for you into English is easy. You can just say,
*by the definition of unitCircle* and other rules of real
arithmetic, the proposition evidently valid. QED.
@@@ -/

/- @@@
### You Can See What Reasoning Principles It Used

For those interested in futher study, Lean has a
ton of options you can set to have it tell you more
or less information as it goes. The following option
tells Lean to tell you what facts the simp tactic uses
in trying to produce a proof for you. Hover over *simp*
(now with a blue underline in VSCode) to see what facts
*simp* used. Don't worry about details, just be happy
you did not have to construct that proof by hand!
@@@ -/

set_option tactic.simp.trace true in

-- hover over simp to see all the definitions it used
example : unitCircle 0 (-1) :=
  by
    simp [unitCircle]


/- @@@
### Proving Propositions About the Real Unit Circle

Now that we have the tools we need to prove propositions
about membership in the unitCircle relation, we should be
all set to prove propositions about membership in the image
of a given set of input values under the unitCircle relation.

We can see that if the input values are {x = 0, x = 1} that
the corresponding set of output values should be {-1, 1, 0}.
If you don't see that, you need to review basic algebra and
confirm that (0, -1), (0, 1), and (1, 0) are the points on
the unit circle with *x = 0* or *x = 1*.

Here's the expression for the image set (of output values)
for the set of input values, { 0, 1}. Hovering over #reduce
gives you the predicate that defines the output/image set.
@@@ -/

#reduce unitCircle.image { 0, 1 }
-- fun y => ∃ x ∈ {0, 1}, unitCircle x y


/- @@@
So now we're set: Let's prove that -1 is in the image
of { 0, 1 } under the unitCircle relation. Here's the
claim/proposition, followed by the proof. As usual, you
cannot just read this proof. Use Lean to interact with
it, to understand the reasoning at each step, what is
left to prove after each step, and how the whole thing
really does (firmly in your mind) prove that one of the
outputs given inputs 0 and 1 is in fact -1.
@@@ -/

example : -1 ∈ unitCircle.image { 0, 1 } :=
/- @@@
By the definition of image, what we have to show is
that ∃ x ∈ { 0, 1 } such that (x, -1) is in the image.
The proof is thus by exists introduction, and we have
to pick a witness that will make the remaining proof
go through. The only value that x/input value in that
set that will work is 0.
@@@ -/
Exists.intro
  0   -- witness
      -- proof
  ( --  prove (0 ∈ {0, 1}) ∧ (unitCircle 0 (-1))
    -- by and introduction
    And.intro
    -- prove: (0 ∈ {0, 1})
    -- { 0, 1 } is represented by the predicate fun n => n = 0 ∨ n = 1
    -- applying fun n => n = 0 ∨ n = 1 to n = 0 is 0 = 0 ∨ 0 = 1
    -- the proof is by left introduction of a proof of 0 = 0
    (
      Or.inl rfl
    )
    -- now what remains to be proved is (unitCircle 0 (-1))
    (
    -- i.e., 0^2 + (-1)^1 = 1
    -- Eq.refl/rfl will *not* work; we can't compute with reals
    -- rather we'll ask Lean to help simplify the goal
    -- which it does, to the point that there's nothing left to prove
        by simp [unitCircle]
    )
  )

/- @@@
### A Few More Useful Tactics

As a final example, let's see how one might construct such a
proof in tactic mode.
@@@ -/

#reduce (types := true) -1 ∈ unitCircle.image { 0, 1 }

example : -1 ∈ unitCircle.image { 0, 1 } :=
by                  -- enter tactic mode
  /- @@@
  We need to show there's an x in { 0, 1 } such that
  (x, -1) is on the unit circle. Clearly x = 0 will do.
  So we use the *apply* tactic to apply the introduction
  rule for exists with 0 as a witness, leaving the proof
  argument to be provided separately. We use an _ to make
  it clear that we're leaving this proof term to be given
  later. Hovering over the _ (or checking the Info View)
  confirms that all that remains to be provided is this
  proof, namely a proof of *0 ∈ {0, 1} ∧ unitCircle 0 (-1)*.
  @@@ -/
  apply Exists.intro 0 _

  /- @@@
  The proof that remains to be provided is a proof of the
  conjunction, *0 ∈ {0, 1} ∧ unitCircle 0 (-1)*. To prove
  it we apply the introduction rule for ∧, leaving the two
  proof arguments to be provided separately. Note that the
  proof context now has two goals pending, one for each of
  the conjuncts.
  @@@ -/
  apply And.intro _ _
  /- @@@
  We can use curly braces and indenting to make tactic-based
  proofs easier to read. Here we prove each conjunct in its
  own { ... } construct.

  @@@ -/
  {
    /- @@@
    The membership predicate here is a disjunction, so we
    apply the rule for Or introduction, here on the left,
    with only a simple equality to prove thereafter.
    @@@ -/
    apply Or.inl _
    apply rfl
  }
  {
    -- The proof of this conjunct is as explained above.
    simp [unitCircle]
  }

/- @@@
Lean provides tactics to automate the application of the
right rules. Here's the same proof again.
@@@ -/
  example : -1 ∈ unitCircle.image { 0, 1 } :=
  by
    use 0         -- give witness for proving ∃
    constructor   -- applies only constructor for goal
    {
      left          -- applies Or.inl
      rfl           -- applies rfl
    }
    simp [unitCircle]

/- @@@
Finally, tactics can be composed into larger tactics.
Here we sequentially compose the tactics from the proof
just given into one big tactic, using ; to compose them.

As you can see, tactics make it easier to give compact
proof construction instructions. The results however are
not always very easy to understand. You have to know what
a lot of tactics do *under the hood*. What you can do to
gain insight is to step through such a tactic-based proof
construction and watch how each steps transforms your
context. Give it a try for yourself, with the Info View
open, put your cursor before each tactic in sequence and
see how the proof state changes until the last remaining
details are given.
@@@ -/


example : -1 ∈ unitCircle.image { 0, 1 } :=
 by use 0; constructor; left; rfl; simp [unitCircle]


/- @@@
## What's Next?

This lesson has introduced you to the formal definition and
principles for reasoning about binary relations. In the next
chapter we will cover a broad range of critical *properties*
of relations, formalized as *predicates on relations*. Such
a property will thus have the type, *Rel α β → Prop*, where,
as we've learned here, *Rel α β* means *α → β → Prop*. So at
bottom we will formalize a property of a binary relation as
a predicate of the type, *(α → β → Prop) → Prop.* Properties
of particular interest include those of being:

- reflexive
- symmetric
- transitive
- equivalence
- well-founded
@@@ -/

end DMT1.Lectures.setsRelationsFunctions.relations
