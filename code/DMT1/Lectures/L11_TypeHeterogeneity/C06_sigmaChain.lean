/- @@@
# Dependent Pair (Sigma) Chains

Idea: Use Σ i, σ i recursively for list-like collections.
Here we convert an n-Sig to such a Type by recursion on n.
@@@ -/

namespace DMT1.Lecture.hetero.hetero

def Sig (n : Nat) := Fin n → Type

-- A heterogeneous n-tuple based on a type signature σ : Fin n → Type
def HChain : (n : Nat) → (σ : Sig n) → Type
  | 0,     _ => Unit
  | n + 1, σ => Σ x : σ ⟨0, Nat.zero_lt_succ n⟩,
                HChain n (fun i => σ ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩)

-- TODO: Examples

/- @@@
Type-safe with different types per position
Good for modeling recursive structures or sequences
Hard to work with.
No constant-time access
Not supportiveo of size-polymorphism
Usea in specific induction-based constructions
@@@ -/

end DMT1.Lecture.hetero.hetero
