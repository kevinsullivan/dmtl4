# Languages

Here are rough notes from our discussion of languages on our first
day of class. 

1. Elements  
   1. Syntax: Symbols and symbolic expressions composed from them
   2. Semantic domains: the things that such symbols/expressions are defined to refer to (also called "denotations")
   3. Interpretations: relations that map symbols to denotations
   4. Semantics: relations that map expressions to denotations
2. Moods
   1. Declarative (indicative): statement asserting what **is** the case ("It is the case that ...")
   2. Optative: statement defining a state that **should be** made to prevail ("I require it to be the case that ...")
   3. Imperative: expresses a **command** to carry out a certain action ("Make it the case that ...")
   4. Conditional: statement asserting what **is** **if** some condition holds ("If X it true, then it's the case that ...")
   5. Subjunctive: expresses uncertainty or **counterfactual** ("If only it were the case that ...")
   6. Exclamatory: an expression of a strong **emotional** state of affairs ("Oh my!")
   7. Interrogative: asks a **question**  ("Is is the case that ...?")
3. Purposes  
   1. Human-Human Communication (e.g., English)
   2. Human-Machine Communication (e.g., Java)
   3. Machine-Machine Communication (e.g., JSON)
   4. Automated reasoning (e.g., program execution, proving)
4. Natural vs Formal Languages  
   1. Natural (ordinary spoken, written, signed human languages):
      1. make human communication easy  
      2. but rigorous expression and reasoning are problematical
      3. ambiguous: shoes must be worn, dogs must be carried
      4. imprecise: keep a *reasonable* distance to the next car
      5. generally not computable (changing with advent of LLMs)  
   2. Formal (logics, mathematicss, programming languages, DSLs)  
      1. human expression and communication require training
      2. strength is suitability for rigorous/mechanical reasoning
      3. Programming, specification, verification, mathematics
   3. Imperative vs Declarative Languages
      1. Imperative  
         1. Step by step procedure to solve a problem
         2. Commands transform mutable states, perform I/O, etc.
         3. Example: Python program for square roots by Newton’s method
         4. Efficiently executable but far from highly expressive  
      2. Declarative  
         1. More expressive than "code" but not as efficiently runnable  
         2. Common features
            1. Syntax and Semantics
            2. Domains, Interpretations, Evaluation  
            3. Models: Validity, Satisfiability, Unsatisfiability  
            4. Expressiveness vs Solvability tradeoffs 
            5. Even decidability of validity of arbitrary expressions  
   4. Formal Language Case Study: Propositional Logic
      1. Syntax (literal, variable, and operator expressions)
      2. Semantic Domain (Boolean algebra)
      3. Interpretations
         1. fixed symbols to Boolean functions
         2. variables to Boolean values
      4. Semantic Evaluation: expressions to Boolean values
      5. Properties of Expressions
         1. validity
         2. satisfiability
         3. unsatisfiability
      6. Computations
         1. model finding
         2. model checking
         3. validity checking
         4. counter-example finding
