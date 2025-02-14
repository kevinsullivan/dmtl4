# Discrete Mathematics and Theory in Lean 4

- [Discrete Mathematics and Theory in Lean 4](#discrete-mathematics-and-theory-in-lean-4)
  - [Acknowledgements](#acknowledgements)
  - [Two Pillars of Computer Science](#two-pillars-of-computer-science)
  - [Stepping Back: Some Problems](#stepping-back-some-problems)
  - [The Secret Sauce](#the-secret-sauce)
  - [Design Constraints](#design-constraints)
  - [The Solution](#the-solution)
  - [An Example](#an-example)
  - [Status](#status)
  - [Lean 4 for CS Pedagogy](#lean-4-for-cs-pedagogy)
  - [Paths Forward](#paths-forward)
  - [Humility](#humility)

## Acknowledgements

![National Science Foundation Logo](./images/480px-NSF_Official_logo_Med_Res.png "National Science Foundation" =100x)

This course was developed with support provided in part by a research grant from the National Science Foundation, #1909414, SHF: Small: Explicating and Exploiting the Physical Semantics of Code.

Any opinions, findings, and conclusions or recommendations expressed in this material are those of the author(s) and do not necessarily reflect the views of the National Science Foundation.

The views expressed in this article are those of the author(s) and do not necessarily reflect the views, policies, or positions of the University of Virginia.

This work expresses cetain technical juddgments by the author based on observation and experience but not always on outcomes of scientific testing. No IRBs have been needed or sought. No student or other human subjects data is reported here or has been reported outside of official reporting channels. 

## Two Pillars of Computer Science

Computation and reasoning are two great intertwined pillars of computer science. Consequently we have languages for expressing *conputations*, namely *programming* languages, and languages for *reasoning* about propositions over diverse structures (or *worlds*). For decades, the computer science fieldhas excelled at teaching computational thinking and skills in reading, writing, and evolving programming code. By contrast, the field has done exceptionally poorly in teaching reasoning and the formal languages and thought processes needed to reason effectively, e.g., about such things as the critical *properties* that software systems should have, e.g., that they are secure.

The use of programming langauges to specify computations is familiar territory even to the earliest computer science students. The very first course in computer science is invariably a course in programming and programming languages. Programming is then one of the primary areas of emphasis throughout the entire undergraduate curriculum. Students of CS thus today generally graduate with high proficiency in computational thinking and in the use of programming languages that support it. 

Recognizing the essential foundational character or reasoning, the *second* course in the undergraduate CS curriculum is typically "CS2: Discrete Mathematics and Theory" (DMT1). It is in this course that students gain their first, and usually their last, exposure to formal reasoning, languages that support it, or applications thereof. Such courses are generally paper-and-pencil affairs covering propositional and first-order logic and set theory, proof construction by induction (but usually only on natural numbers), and maybe a few related topics, such as graphs and combinatorics.

The problem that this course addresses has two parts. On the supply (of talent) side, the problem is that, as far as this researcher and educator see, students almost invariably find these courses to be boring, abstract, disconnected from their interest in computing, and deeply forgettable. Anecdotally, most graduate students incoming to this researchers courses remember almost nothing from their early DMT courses, and few have ever had to use reasoning langauges and methods after taking DMT1.

On the demand side, we are now seeing very rapidly growing demand for graduating engineers who do actually understand formal reasoning and languages, but the supply is miniscule. This explosion in demand for reasoning skills is happening at the same time we're seeing a drop-off in demand for "mere" computational thinking and programming.

The conclusions of the author include the following: (1) Our field has failed to train generations of graduating computer scientists in the thought processes and the formal languages needed to be productive with *reasoning* in advanced industrial practice. (2) The standard DMT1 course is, for far too many students, not a productive or memorable experience, as evinced by ample observation of the exceptionally poor state of knowledge of most incoming graduate students in computer science, in the author's experience. (3) It is time to replace the standard DMT1 course with something entirely new, different, and far better. 

The course presented here is offered as a model for an entirely new approach. At the highest level, it teaches all of the core material in any DMT1 course but with all of the context formalized in the reasoning language, Lean 4. In languages like this, supported by wonderful tooling, reasoning is linked to comptuation by the amazing unification known as the the *Curry-Howard Correspondence* (CHC). The CHC holds that formalized deductive reasoning of certains kinds (natural deduction, which is perhaps the core concept in any DMT course) is a form of computing, but not only with the usual data and function types but with now axioms, propositions, and proofs as first-class citizens. 

Lean 4 is so beautifully expressive of such a broad range of mathematical concepts that a significant community of mathematicians have organized around it to drive the development of formalized versions of mathematics across a very broad range of fields. Meanwhile, CS students remain stuck learning a logic (first-order predicate logic and set theory) that is *not* suitable as a foundation for formalizing abstract mathemtics in a way that makes it readily mechanizabe. This course adopts, *type theory*, here as implemented by Lean 4, as a far better choice even for early CS students.

## Stepping Back: Some Problems

That we've arrived at a point where reasoning technology is advancing at extraordinary speed but where are students are by and large entirely unprepared to understand or use it. Of course, for many decades, the demand for programming was voracious, and at the same time cost and difficulty of reasoning were prohibitively high. But now the tables are turned. Generative and related AI promise to reduce demand for programming code while the needs of industry and national security are driving significant increases in demand for formal reasoning. 

This course aims to help address the resulting shortfall in talent by radically replacing the traditional undergraduate DMT1 course with a new one, covering essentiall the same basic content, but now using the wildly successful reasoning and computation language and toolset of Lean 4. The course is scoped for a full undergraduate semester or as the first half of an introductory graduate course in formal languages and reasoning. Big changes in in circumstances make now a great time to consider such a transition in CS pedagogy. They include the following:

- Rapidly increasing industrial demand for formal, machine-supported and machine-checked reasoning about critical properties software-intensive systems that undergird our society
- The emergence of type-theory-based formalisms with exceptional expressiveness and broad applications that have attracted large communities of researchers in mathematics, which gtends to validate the proposition that there's something new and remarkable in them
- The development of superb tooling for using reasoning languages effectively in practice
- The profound intertwining of computation and reasoning afforded by such langauges
- The real possibility that mere routine programming will increasingly be done by "AIs"

## The Secret Sauce

Perhaps key insight behind the design of this course is that the Curry-Howard correspondence provides the essential bridge to connect students' intrinsic interest in computing with what hitherto had been arcane and apparently not very useful or in-demand subject matter. The course by contrast emphasizes the essential computational nature of logical reasoning. After teaching semantic validity for simple propositional logic, with an emphasis on a subset of propositional forms that emerge as the axioms of deducative reasoning in predicate logic, the course moves directly into predicate logic as embedded in the type theory of the Lean 4 prover.

A second design principle is that all of the concepts to be taught must be teachable in the main formal logic taught in the course. First-order logic just won't do in this regard. In first-order predicate logic, for example, one can state what it means for a particular relation to be symmetric, but one cannot formalize what it means for any binary relation on a set to be symmetric because, of course, one cannot quantify over relations. And yet it is this more abstract kind of reasoning that students need to learn. The course assumes that higher-order predicate logic embedded in type theory with inductive definitions, e.g., using Lean 4, is far preferable to spending the better part of a semester on first-order theory, in which one cannot formalize even the content of the course in which it's being taught. We now know how to formalize mathematics. Use Lean, or Roqc, or something similar.

## Design Constraints

This course was developed under a few key constraints:

- Continue to focus on the basic content of the traditional course: logic, sets, induction
- Avoid assiduously overwhelming early students with the complexity of modern proof assistants
- Formalize every concept in the uniform logic of the proof assistant using conventional notations
- Ensure that first-order theory is a special case of the more expressive theory of the course
- Provide students with a deeply computational perspective, from great tooling to Curry-Howard 

## The Solution

The solution, now tested in practice, has a few key elements:

- Make the standard embedding of predicate logic in Lean the main logic students learn
- Begin with a deep embedding of propositional logic syntax, semantics, and validity in Lean 4
- Thoroughly cover all of the axioms for reasoning in predicate logic as its embedded in Lean 4
- Build all of the material on sets, relations, and properties thereof on top of this logic
- Present induction first as a way to build programs, and only later on as a way to build proofs
- Aggressively limit covereage of Lean; e.g., the tactic language is off the table until the end

## An Example

Here are two simple examples of what students will see in this course. The first illustrates how students would write propositional logic expressions. The second gives an example of how they would write, and then use, the definition of a certain property of a relation.

First, this is a snippet of some "code" for propositional logic, the syntax and semantics of which they have seen how to specify.

- def andAssociative  := ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R))
- def equivalence     := (P ↔ Q) ↔ ((P ⇒ Q) ∧ (Q ⇒ P))

Second, here's an example of the specification of the property of a relation being well founded.

- def isWellOrdering  {α  β : Type} : Rel α α → Prop := fun r => ∀ (s : Set α), s ≠ ∅ → ∃ m, (m ∈ s ∧ ¬∃ n ∈ s, r n m)

By the end of the course students should be able to read and explain what this definition means, with an explanation roughly as follows. A relation, r, on a set, α, is said to be well ordered if any non-empty set of α values has a least element. That is, there is some m in the set such that there is no other value, n, in the set that is "less than" m under r.

## Status

The status of this online book is *emerging*. In this spring of 2025, the author is teaching an introductory graduate course called *software logic.* As nearly all graduate students in the class have no meaningful background in reasoning languages and practice, the undergraduate course is the first major part of the graduate course. As the semester goes along, more and more fo the undergraduate course material from previous semesters will appear here.  Check back once in a while for updates if you're interested.

## Lean 4 for CS Pedagogy

Lean 4 has thoroughly proven itself as an outstanding language for the clear, concise, and useful formalization of abstract mathematics, far beyond what is needed in a first course in discrete mathemtics and theory. That said, it's an exceptionally good vehicle for teaching this course because it's fabulously and naturally expressive of the ideas to be taught (unlike first-order theory); it engaged students through their interest in computation and computational tools; and it sets student on a path not only to firmer intellectual foundations but to a new era in computer science, with AIs taking over routine programming and humans now increasingly needed for complex reasoning about programs.

## Paths Forward

From here, advanced courses in several areas are possible at both undergraduate and graduate levels, including programming language design and implementation, software verification, provable security, machine learning (e.g., see AlphaProof), and ultimately the higher mathematics of robotics, quantum computing, cyber-physical systems, control systems, concurrent systems, and many other domains. 

## Humility

There are issues and opportunities for improvement at all levels of this document, from the lexical to the conceptual. If you feel inclined to provide input, even of the more critical variety, please don't hesitate to send it along.

&copy; Kevin Sullivan 2024-2025.
