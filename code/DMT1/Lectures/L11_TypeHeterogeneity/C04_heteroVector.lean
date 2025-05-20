/- @@@
# Dependently Typed (Heterogeneous) Vectors
@@@-/

namespace DMT1.Lecture.hetero.hetero

inductive DVec : (n : Nat) → (σ : Fin n → Type u) → Type (u + 1)
  | nil {σ : Fin 0 → Type u} : DVec 0 σ
  | cons {n : Nat} {σ : Fin (n + 1) → Type u} :
      σ 0 →
      DVec n (fun i => σ (Fin.succ i)) →
      DVec (n + 1) σ

def DVec.get {n : Nat} {σ : Fin n → Type u} (xs : DVec n σ) (i : Fin n) : σ i :=
  match xs, i with
  | DVec.cons x _, ⟨0, _⟩     => x
  | DVec.cons _ xs', ⟨i'+1, h⟩ =>
      xs'.get ⟨i', Nat.lt_of_succ_lt_succ h⟩

def mySig : Fin 3 → Type
  | ⟨0, _⟩ => Nat
  | ⟨1, _⟩ => Bool
  | ⟨2, _⟩ => String

def myDVec : DVec 3 mySig :=
  DVec.cons (42 : Nat) (DVec.cons true (DVec.cons "hello" DVec.nil))

#eval myDVec.get ⟨0, by decide⟩  -- 42
#eval myDVec.get ⟨1, by decide⟩  -- true
#eval myDVec.get ⟨2, by decide⟩  -- "hello"


open DVec

def DVec.reprDVec {n : Nat} {σ : Fin n → Type u} (inst : ∀ i, Repr (σ i)) :
    DVec n σ → String
  | DVec.nil => "[]"
  | @DVec.cons n' σ' x xs =>
    let head := Std.Format.pretty (repr x)
    let tail := DVec.reprDVec (fun i => inst (Fin.succ i)) xs
    "[" ++ head ++ "," ++ tail.dropWhile (· == '[')   -- TODO: extra , after last elt

instance {n : Nat} {σ : Fin n → Type u} [∀ i, Repr (σ i)] : Repr (DVec n σ) where
  reprPrec xs _ := Std.Format.text (DVec.reprDVec (inst := inferInstance) xs)

instance {n : Nat} {σ : Fin n → Type u} [∀ i, Repr (σ i)] : ToString (DVec n σ) where
  toString xs := DVec.reprDVec (inst := inferInstance) xs

/- @@@
Lean does not synthesize ∀ i, Repr (σ i) even if it knows each Repr (σ i)
separately. We help it by hand-writing the dependent function instance.
@@@ -/
instance : ∀ i : Fin 3, Repr (mySig i)
  | ⟨0, _⟩ => inferInstanceAs (Repr Nat)
  | ⟨1, _⟩ => inferInstanceAs (Repr Bool)
  | ⟨2, _⟩ => inferInstanceAs (Repr String)

#eval myDVec

/- @@@
-Precise and compositional
- Access by Fin i
- Allows index-aligned computations
- Boilerplate-heavy
- Requires dependent recursion for construction and access
- Good for index-typed languages, embedded DSLs, typed syntax trees
@@@ -/

end DMT1.Lecture.hetero.hetero
