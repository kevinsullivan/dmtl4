from z3 import *

# declare names for 3 distinct Z3 integer variable expressions
C = Int('C')
D = Int('D')
R = Int('R')

# you must buy at least one of each kind of animal
# propositions in the language of propositional logic 
# with arithmetic relations
cats_constraint =  C >= 1 
dogs_constraint =  D >= 1 
rodents_constraint = R >= 1 

# you must buy 100 animals total
total_animals_constraint =  C + D + R == 100 

# cats cost $1.00; dogs, $15, and rats, $0.25
cat_price = 100
dog_price = 1500
rat_price = 25

# the total cost must be exactly $100.00
total_cost_constraint =  cat_price * C  + dog_price * D + rat_price * R == 10000 

# the problem is to find values for C, D, and M that satisfy all of these conditions
# our overall specification is the "and" of all of the individual constraints
problem_specification = \
    And (
        cats_constraint, \
        dogs_constraint, \
        rodents_constraint, \
        total_animals_constraint, \
        total_cost_constraint \
    )


s = Solver()

s.add(problem_specification)

print("The PLA problem,", problem_specification, ", is", s.check())
if (s.check() == sat):      # otherwise we'd get a runtime exception
    print("Here's a satisfying solution (a model): ", s.model())

