module

public import Oberwolfach.PermutationClose
public import Mathlib.Data.Sym.Sym2

@[expose] public section

/-! Distinct physical edges in a separated successor tuple. The closing
edge uses the successor of the first label; it is not silently identified
with an ordinary auxiliary edge. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def PermutationSeparated {I V : Type*} (π : Equiv.Perm V) (b : ℕ) (f : I → V) : Prop :=
  ∀ i j, i ≠ j → ¬ PermutationClose π b (f i) (f j)

theorem permutationSeparated_injective {I V : Type*}
    (π : Equiv.Perm V) (b : ℕ) (f : I → V) (h : PermutationSeparated π b f) :
    Function.Injective f := by
  intro i j he
  by_contra hij
  exact h i j hij (Or.inl he)

theorem permutationSeparated_successor_avoid {I V : Type*}
    (π : Equiv.Perm V) (b : ℕ) (hb : 1 ≤ b) (f : I → V)
    (h : PermutationSeparated π b f) (i j : I) (hij : i ≠ j) :
    π (f i) ≠ f j := by
  intro he
  apply h i j hij
  exact Or.inr ⟨⟨0, by omega⟩, Or.inl (by simpa using he)⟩

def twistedTupleEdge {c : ℕ} {V : Type*} (f : Fin (c + 1) → V) (z : V) :
    Fin c ⊕ Unit → Sym2 V
  | Sum.inl i => s(f i.castSucc, f i.succ)
  | Sum.inr _ => s(f (Fin.last c), z)

theorem twistedTupleEdge_injective {c : ℕ} (hc : 2 ≤ c) {V : Type*}
    (f : Fin (c + 1) → V) (hf : Function.Injective f) (z : V)
    (hz : ∀ i : Fin (c + 1), i ≠ 0 → z ≠ f i) :
    Function.Injective (twistedTupleEdge f z) := by
  have hpath (i j : Fin c) (h : s(f i.castSucc, f i.succ) = s(f j.castSucc, f j.succ)) : i = j := by
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · apply Fin.ext
      have hi := congrArg Fin.val (hf h1)
      simpa only [Fin.val_castSucc] using hi
    · have hi := congrArg Fin.val (hf h1)
      have hj := congrArg Fin.val (hf h2)
      simp only [Fin.val_castSucc, Fin.val_succ] at hi hj
      omega
  have hlast (i : Fin c) : s(f i.castSucc, f i.succ) ≠ s(f (Fin.last c), z) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hi := congrArg Fin.val (hf h1)
      simp only [Fin.val_castSucc, Fin.val_last] at hi
      omega
    · have hi : i.castSucc = 0 := by
        by_contra hne
        exact hz i.castSucc hne h1.symm
      have hj := congrArg Fin.val (hf h2)
      have hi' := congrArg Fin.val hi
      simp only [Fin.val_castSucc, Fin.val_zero, Fin.val_succ, Fin.val_last] at hi' hj
      omega
  intro x y h
  cases x with
  | inl i =>
    cases y with
    | inl j => exact congrArg Sum.inl (hpath i j h)
    | inr u => exact (hlast i h).elim
  | inr u =>
    cases y with
    | inl j => exact (hlast j h.symm).elim
    | inr v => congr

theorem separated_successor_edges_injective {c : ℕ} (hc : 2 ≤ c) {V : Type*}
    (π : Equiv.Perm V) (b : ℕ) (hb : 1 ≤ b) (f : Fin (c + 1) → V)
    (h : PermutationSeparated π b f) :
    Function.Injective (twistedTupleEdge f (π (f 0))) :=
  twistedTupleEdge_injective hc f (permutationSeparated_injective π b f h) _
    (fun i hi => permutationSeparated_successor_avoid π b hb f h 0 i hi.symm)

end Oberwolfach
