# Predicate Logic

Whereas propositions (expressions) in propositional
logic have only Boolean values as their semantic domain,
expressions in predicate logic are interpreted over much
richer representations that express worlds as comprising
entities, functions between, and relations over entities.
One can speak about much more complex worlds in predicate
logic than in propositional logic. 

For example, one might want to discuss what properties
the "friend" relation should have on some novel social
networking system? On FB, it's symmetric, for example.
But "follows" on other networks often isn't symmetric.
Higher-order predicate logic in Lean is a remarkably
nice language in which to speak of such things. We can
for example say that *r* is any binary relation on any
set *s* of objects of any type *T*, then what we mean
when we say *symmetric r* is that for any two values,
*s* and *t*, from *T*, if *r* relates *s* to *t* then
it also relates *t* to *s*. It will be clear why it is
possible to express this natural idea formally in Lean
but not in first-order set theory. The Logic of Lean is
a better one to learn first than first-order theory in
that it enables the formal expression and manipulation
of a lot of material that remains outside the formalisms
students are taught in first-order theory-baed classes.
To see it not only internalized in Lean but mechanized
for subsequent reasoning tasks can be pretty rewarding.
