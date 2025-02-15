# Discrete Mathematics and Theory in Lean 4

- [Discrete Mathematics and Theory in Lean 4](#discrete-mathematics-and-theory-in-lean-4)
  - [Acknowledgements](#acknowledgements)
  - [Disclaimers](#disclaimers)
  - [A Couple of Pillars](#a-couple-of-pillars)
  - [Some Problems](#some-problems)
  - [Secret Sauce](#secret-sauce)
  - [Design Constraints](#design-constraints)
  - [This Solution](#this-solution)
  - [An Example](#an-example)
  - [Status](#status)
  - [Invitation](#invitation)
  - [Errata](#errata)
  - [Student Paths Forward](#student-paths-forward)
  - [Humility](#humility)
  - [Research Path Forward](#research-path-forward)

## Acknowledgements

![National Science Foundation Logo](./images/480px-NSF_Official_logo_Med_Res.png "National Science Foundation" =100x)

This course was developed with support provided in part by a research grant from the National Science Foundation, #1909414, SHF: Small: Explicating and Exploiting the Physical Semantics of Code.

## Disclaimers 

Any opinions, findings, and conclusions or recommendations expressed in this material are those of the author(s) and do not necessarily reflect the views of the National Science Foundation.

The views expressed in this article are those of the author(s) and do not necessarily reflect the views, policies, or positions of the University of Virginia.

This work expresses cetain technical juddgments by the author based on observation and experience but not always on outcomes of scientific testing. No IRBs have been needed or sought. No student or other human subjects data is reported here or has been reported outside of official reporting channels. 

## A Couple of Pillars

Computation and systematized reasoning are two great intertwined pillars of computer science. Consequently we have languages for expressing *conputations*, namely *programming* languages, and languages for *reasoning* about propositions over diverse *worlds*. For decades, we in computer science have excelled at teaching computational thinking and the use of programming languages. By contrast, we have done exceptionally poorly in teaching reasoning and the formal languages and thought processes needed to reason formally in practice.

The use of programming langauges is familiar territory even to the earliest computer science students. The very first course in computer science is invariably a course in programming, and implicitly in programming languages. Programming then remains one of the primary areas of emphasis throughout the entire undergraduate curriculum. Students of CS thus today generally graduate with high proficiency in computational thinking and in the use of programming languages that support it.

Recognizing the essential foundational character or reasoning, the *second* course in the undergraduate CS curriculum is typically called something like CS2: Discrete Mathematics and Theory (DMT1). It is in this course that students gain their first, and sadly usually their last, exposure to formal reasoning and languages and systems that support it. Such courses are generally paper-and-pencil affairs covering propositional logic, first-order predicate logic and set theory, and induction (but usually only on natural numbers).

The problem with the ubiquity of such courses are many. First, CS students tend ot find these courses boring, abstract, disconnected from their intrinsic motations to learn about computing, irrelevant to practice, and deeply forgettable.  Anecdotally, most students entering graduate programs in CS appear remember almost nothing from their early DMT courses, and few have ever had to use reasoning langauges and methods after DMT1.

On the demand side, on the other hand, we are now seeing rapidly growing needs for engineers who do actually understand formal reasoning and languages. On the other hand, the supply of such talent is miniscule, due in large part to the failure to train our students in such knowledge and skills. Moreover, this explosion in demand for reasoning skills is happening at the same time we're seeing a significant drop-off in demand for "mere" computational thinking and programming.

The conclusions of the author include the following: (1) Our field has failed to train generations of graduating computer scientists in the thought processes and the formal languages needed to be productive with *reasoning* in theory or industrial practice. (2) The standard DMT1 course is, for far too many students, not a productive or memorable experience, as evinced by the exceptionally poor state of knowledge of most incoming graduate students in computer science (in the author's experience). (3) It is time to replace the standard DMT1 course with something entirely new, different, and far better. (4) It is time to think about re-balancing the entire undergraduate curriculum toward greater emphasis on mathematical abstractions and formal reasoning.

The course presented here is thus offered as a model for an entirely new approach. At the highest level, it teaches all of the core material in any DMT1 course but with all of the context formalized in the reasoning language, Lean 4. In languages like this, supported by wonderful tooling, reasoning is linked to comptuation by the amazing unification known as the the *Curry-Howard Correspondence* (CHC). The CHC holds that formalized deductive reasoning of certains kinds (natural deduction, which is perhaps the core concept in any DMT course) is a form of computing, but not only with the usual data and function types but with now axioms, propositions, and proofs as first-class citizens. 

Lean 4 is so beautifully expressive of such a broad range of mathematical concepts that a significant community of mathematicians have organized around it to drive the development of formalized versions of mathematics across a very broad range of fields. Meanwhile, CS students remain stuck learning a logic (first-order predicate logic and set theory) that is *not* suitable as a foundation for formalized or automated abstract mathemtics. This course, on the other hand, adopts, *type theory*, here as implemented by Lean 4, as a far better choice, even for early CS students.

## Some Problems

That we've arrived at a point where reasoning technology is advancing at extraordinary speed but where are students are by and large entirely unprepared to understand or use it. Of course, for many decades, the demand for programming was voracious, and at the same time cost and difficulty of reasoning were prohibitively high. But now the tables are turned. Generative and related AI promise to reduce demand for programming code while the needs of industry and national security are driving significant increases in demand for formal reasoning. 

This course aims to help address the resulting shortfall in talent by radically replacing the traditional undergraduate DMT1 course with a new one, covering essentiall the same basic content, but now using the wildly successful reasoning and computation language and toolset of Lean 4. The course is scoped for a full undergraduate semester or as the first half of an introductory graduate course in formal languages and reasoning. Big changes in in circumstances make now a great time to consider such a transition in CS pedagogy. They include the following:

- Rapidly increasing industrial demand for formal, machine-supported and machine-checked reasoning about critical properties software-intensive systems that undergird our society
- The emergence of type-theory-based formalisms with exceptional expressiveness and broad applications that have attracted large communities of researchers in mathematics, which gtends to validate the proposition that there's something new and remarkable in them
- The development of superb tooling for using reasoning languages effectively in practice
- The profound intertwining of computation and reasoning afforded by such langauges
- The real possibility that mere routine programming will increasingly be done by "AIs"

## Secret Sauce

The idea is to simultaneously gain a deeper understanding of reasoning while also
seeing it as a form computation, albeit now over reasoning rather than computational
terms. For example, we begin with propositional logic---syntax, semantics, validity,
soundness, etc.--through its standard deep embedding into (the logic of) Lean 4. A
demonstrated strength of Lean 4 is in its enabling communities to express rich theories
in the clear, abstract, generalized terms of the particular domain itself, across a wide
range of domains in graduate- and beyond-level mathematics. 

The entire course is set up this way. Predicate logic is presented through its standard 
shallow embedding in Lean 4. First-order logic is described as a special case. 

This course  can then teach general concepts as being general, with reflexivity of a
binary relation on a set as an example. In a first-order course, you can formally express
the what it means for some particular set, s, and some particular binary relation, r on
s, for r to be "reflexive." That's ok, but it expands one's mathematical agility to be
able to say, and express formally that reflexivity is a property of *any* binary
relation r on *any* set s of objects of *any* type, T. The expressiveness of first-order
logic is well short of being able to express many of the most important ideas expected
to be taught in this class.

It's not just a nicety, either, to have *reflexive* as a predicate on any binary relation
on any set of terms of any type. It means that this predicate can be applied to any 
particular relation so as to produce the proposition that it is reflexive,. The 
application of predicates to particulars in this manner is ubiquitous in formal 
reasoning, reading, and writing. Being able to formally state propositions about relations by applying predicates to them and then also knowing how
to construct machine-checked proofs of them can perhaps be taken as evidence of deeper
undertanding and broader potential to use formal reasoning productively in practice.
 
Another principle is that all of the core concepts taught in the traditional course must
be taught in the new course: propositional logic, predicate logic, sets, induction. This
course covers the same topics but in different ways. For example, induction is first seen
as a way to construct recursive functions. Later the same machine is used to construct 
recursive proof terms.

The deepest difference is that this course is rooted in type theory, whereas first-order
set theory and predicate logic are the foundations for the traditional course. This course
instead teaches sets theory as embedded in Lean with one-place predicates both specifying
and subsequently representing sets. With standard concrete notations, set theory in Lean
appears to be *plenty good enough* for teaching CS2-level set concepts. And the pleasures
of having all of this content being handled by Lean, rather than by oneself using paper and 
pencil, are significant.

## Design Constraints

This course was developed under a few key constraints:

- Continue to focus on the basic content of the traditional course: logic, sets, induction
- Avoid assiduously overwhelming early students with the complexity of modern proof assistants
- Formalize every concept in the uniform logic of the proof assistant using conventional notations
- Ensure that first-order theory is a special case of the more expressive theory of the course
- Provide students with a deeply computational perspective, from great tooling to Curry-Howard 

## This Solution

The solution, now tested in practice (but not scientifically evaluated yet), has a few 
key elements:

- Make standard embeddings propositional and predicate logic in Lean a path to Lean 4 itself
- Begin with a deep embedding of propositional logic syntax, semantics, and validity in Lean 4
- Thoroughly cover all of the axioms for reasoning in predicate logic as its embedded in Lean 4
- Build all of the material on set theory (sets, relations, properties) on top of this logic
- Present induction first as a way to build functions and only later as a way to build proofs
- Minimize covereage of complex or inessential Lean; e.g., tactics are omitted until the end

## An Example

Here are two simple examples of what students might see in this course.

The first  illustrates how students would write propositional logic expressions.

- def andAssociative  := ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R))
- def equivalence     := (P ↔ Q) ↔ ((P ⇒ Q) ∧ (Q ⇒ P))

This one, second, specifies the generalized property of a relation of being well ordered.

- def isWellOrdering  {α  β : Type} : Rel α α → Prop := fun r => ∀ (s : Set α), s ≠ ∅ → ∃ m, (m ∈ s ∧ ¬∃ n ∈ s, r n m)

By the end of the course students should be able to read and explain what this definition 
means, and *apply* it to particulars in the process of making richer claims about them.
The undergraduate does emphasize from start to finish practicing the skill of translating
between formal and *natural* natural language.

## Status

The status of this online book is *now drafted and under revisions: work in progress*. In
this spring of 2025, the author is teaching an introductory graduate course called *software
logic.* The undergraduate course presented here is now serving the dual purpose of getting
graduate students up to speed, but now with added content and at double speed. By the end
of this semester, the online document should be a reasonable polished presentation of the
undergraduate course. Most of the raw material is already online but only in a raw and not
previously disseminated form from last semester's undergraduate course.

## Invitation

If you with to discuss these materials, drop me a line with DMTL4 as the subject line.
It's my last name at Virginia, Edu.

## Errata

If you want to alert us to errors in these materials, feel free to deposit an issue
in the course repository (currently, Feb 2025) on GitHub.

## Student Paths Forward

From here, advanced courses in several areas are possible at both undergraduate and graduate
levels: cyberphysical systems, programming language design and implementation, verification,
provable security, machine learning (e.g., see AlphaProof), robotics, quantum computing, etc.

## Humility

There are surely problems and opportunities for improvement throughout this document. If you 
feel inclined to provide input, please do send it along.

## Research Path Forward

Natural experiment.

&copy; Kevin Sullivan 2024-2025.
