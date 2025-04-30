/- @@@
- Extends makes the named class a field of the one being defined.
- set_option trace.Meta.synthInstance true
- An easy way to see what are the fields of our classes is to check their constructor
- the type class system assumes every type has only one instance of each type class
- May 9
- each class appearing in the extends clause should mention every type appearing in the parameters
- ring tactic, group tactic, abel tactic for abelian groups
- having multiple actions of the same group on the same type requires some contortions, such as defining type synonyms, each of which carries different type class instances.
@@@ -/


/-
/- @@@
### VAdd
@@@ -/

/- @@@
### VAdd (Vc α n) (Vc α n)

Question need for this, and design appropriateness.

-- defines +ᵥ on *vectors* (seems not quite right)
instance [Add α] : VAdd (Vc α n) (Vc α n) where
  vadd v p := ⟨ v.1 + p.1 ⟩

-- SIMP ENABLED
-- @[simp]
theorem Vc.vadd_def [Add α] (v : Vc α n) (p : Vc α n) :
  v +ᵥ p = ⟨ v.1 + p.1 ⟩ := rfl
@@@ -/

-/
