# Languages

Computer science is deeply connected with the concept of languages,
particularly formal languages, which are languages where the valid
forms of expressions are precisely specific, unlike so-called natural
languages, such as English, where one typically has greater expressive
freedom.

In this course, we will distinguish between two varieties of formal
languages, in turn. Languages in the first class are mostly intended
to support the specification of practical *computations*. These are
the *programming* languages. The languages in the second class are
weighted toward the expression of propositions, or claims about some
work, and reasoning about them.

## Elements

A language consists of several essential components that define its structure and meaning. These include:

- **Syntax**: The formal arrangement of symbols and symbolic expressions.
- **Semantic Domains**: The entities to which symbols and expressions refer, commonly referred to as denotations.
- **Interpretations**: The mappings that relate symbols to their denotations.
- **Semantics**: The relations that map entire expressions to their corresponding denotations.

Understanding these elements is fundamental to both natural and formal languages, as they provide the foundation for meaning and interpretation.

## Moods

Languages can be classified by their **moods**, which reflect different communicative intents:

- **Declarative (Indicative)**: Used to assert statements about reality (e.g., "It is the case that ...").
- **Optative**: Expresses a desired state of affairs (e.g., "I require it to be the case that ...").
- **Imperative**: Issues commands to achieve a certain action (e.g., "Make it the case that ...").
- **Conditional**: Specifies a dependency between conditions and outcomes (e.g., "If X is true, then it is the case that ...").
- **Subjunctive**: Expresses counterfactuals or uncertainty (e.g., "If only it were the case that ...").
- **Exclamatory**: Conveys strong emotions (e.g., "Oh my!").
- **Interrogative**: Seeks information through questioning (e.g., "Is it the case that ...?").

## Purposes

Different languages serve different functional purposes, including:

- **Human-Human Communication**: Facilitating communication between people (e.g., English, Mandarin).
- **Human-Machine Communication**: Enabling humans to issue instructions to machines (e.g., Java, Python).
- **Machine-Machine Communication**: Standardized formats for automated data exchange (e.g., JSON, XML).
- **Automated Reasoning**: Languages designed for formal reasoning, program execution, and proof verification.

## Natural vs. Formal

### Natural Languages

Natural languages—such as English, Spanish, and Mandarin—evolve to maximize ease of communication among humans. However, they introduce challenges in rigorous reasoning due to inherent properties:

- **Ambiguity**: A single phrase may have multiple interpretations (e.g., "Shoes must be worn, dogs must be carried").
- **Imprecision**: Some instructions lack formal specificity (e.g., "Keep a reasonable distance from the next car").
- **Computational Complexity**: While natural languages have historically been difficult to process computationally, large language models (LLMs) are changing this dynamic.

### Formal Languages

Formal languages—such as those used in logic, mathematics, and programming—are designed for precision and mechanical reasoning. Their primary benefits include:

- **Rigor**: Supporting exact definitions and structured reasoning.
- **Computability**: Enabling automated processing and verification.
- **Application Scope**: Used in programming, specification, verification, and mathematical proofs.

## Imperative vs. Declarative 

### Imperative Languages

Imperative languages define step-by-step procedures for solving problems. These languages execute commands that transform mutable states and perform I/O operations. A classic example is a Python implementation of Newton’s method for computing square roots.

While imperative languages enable efficient execution, they often lack expressiveness compared to declarative approaches.

### Declarative Languages

Declarative languages emphasize expressiveness over step-by-step execution. Key characteristics include:

- **Syntax and Semantics**: Clearly defined structure and meaning.
- **Domains, Interpretations, and Evaluation**: A well-defined mapping between symbols and their interpretations.
- **Models**:\n  - **Validity**: An expression is valid if it is true under all interpretations.
  - **Satisfiability**: An expression is satisfiable if at least one interpretation makes it true.
  - **Unsatisfiability**: An expression is unsatisfiable if no interpretation makes it true.
- **Expressiveness vs. Solvability Trade-offs**: More expressive languages tend to pose greater computational challenges.
- **Decidability**: The problem of determining the validity of arbitrary expressions may be undecidable in some cases.

## Formal Language Case Study: Propositional Logic

A classic example of a formal language is **propositional logic**, which serves as a foundation for automated reasoning.

### Syntax

Propositional logic consists of:

- **Literals**: Atomic Boolean values (e.g., `true`, `false`).
- **Variables**: Symbols that represent Boolean values (e.g., `P`, `Q`).
- **Operators**: Logical connectives such as `AND`, `OR`, `NOT`, `IMPLIES`.

### Semantic Domain

Propositional logic is grounded in **Boolean algebra**, where expressions evaluate to either `true` or `false`.

### Interpretations

- **Fixed Symbols**: Operators map to specific Boolean functions.
- **Variables**: Assigned Boolean values in a given interpretation.

### Semantic Evaluation

Expressions are evaluated within a given interpretation, determining their truth values.

### Properties of Expressions

- **Validity**: An expression is valid if it evaluates to `true` in all interpretations.
- **Satisfiability**: An expression is satisfiable if there exists at least one interpretation where it evaluates to `true`.
- **Unsatisfiability**: An expression is unsatisfiable if it evaluates to `false` in all interpretations.

### Computations in Propositional Logic

Several computational tasks arise in propositional logic:

- **Model Finding**: Identifying an interpretation that satisfies a given expression.
- **Model Checking**: Verifying whether an interpretation satisfies a given expression.
- **Validity Checking**: Determining whether an expression is valid.
- **Counterexample Finding**: Identifying interpretations that falsify an expression.

### Conclusion

Languages—whether natural or formal—play an essential role in communication, computation, and reasoning. While natural languages prioritize human usability, formal languages enable rigorous expression and mechanical processing. The study of formal languages, including logic and programming languages, continues to shape advancements in computing, verification, and artificial intelligence.
