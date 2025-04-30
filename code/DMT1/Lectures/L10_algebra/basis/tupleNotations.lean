namespace TupleNotations

open Fin

-- Raw function Fin n → T
notation "[" l:(foldr `, ` (h t => h :: t) []) "]ₘ" =>
  (fun i => l.get! i.val)

-- Tuple structure
notation "[" l:(foldr `, ` (h t => h :: t) []) "]ₜ" =>
  { toFun := fun i => l.get! i.val }

-- Vc structure
notation "[" l:(foldr `, ` (h t => h :: t) []) "]ᵥ" =>
  ⟨{ toFun := fun i => l.get! i.val }⟩

end TupleNotations

open TupleNotations

#check ([1,2,3]ₘ : Fin 3 → ℕ)
#check ([1,2,3]ₜ : Tuple ℚ 3)
#check ([1,2,3]ᵥ : Vc ℚ 3)
