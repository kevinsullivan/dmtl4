
In Lean, the general concept of an additive group action
is specified by the AddAction typeclass. Instantiating this
class will provide the +ᵥ notation, shorthand for *vadd,*
the operation that will apply an action to an object. This
typeclass will turn rotations into actions on robots.
@@@ -/

#check AddAction

/- @@@
```lean
class AddAction (G : Type*) (P : Type*) [AddMonoid G] extends VAdd G P where
  /-- Zero is a neutral element for `+ᵥ` -/
  protected zero_vadd : ∀ p : P, (0 : G) +ᵥ p = p
  /-- Associativity of `+` and `+ᵥ` -/
  add_vadd : ∀ (g₁ g₂ : G) (p : P), (g₁ + g₂) +ᵥ p = g₁ +ᵥ g₂ +ᵥ p
```
@@@ -/

/- @@@
We can see that the *AddAction* typeclass is parameterized by two
types: *G* and *P*. *G* will be our group of actions (here required
only to be a monoid). *P* will be the type of objects acted upon.
To instantiate the class, we will need three elements:

- an instance of the *VAdd* class, defining (overloading) +ᵥ
- show that the group zero element is "no action"
- show that applying a sum of actions is the same as one at a time
