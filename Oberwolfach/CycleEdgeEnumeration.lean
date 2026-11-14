module

public import Oberwolfach.CycleCopies

@[expose] public section

/-! Each edge of an embedded cycle is indexed exactly once by a cyclic step. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def cycleNext {r : ℕ} (i : Fin r) : Fin r :=
  ⟨(i.val + 1) % r, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

theorem cycleNext_val {r : ℕ} (i : Fin r) :
    (cycleNext i).val = if i.val + 1 < r then i.val + 1 else 0 := by
  dsimp only [cycleNext]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have hi : i.val + 1 = r := by omega
    rw [hi, Nat.mod_self]

theorem cycleNext_two_ne {r : ℕ} (hr : 3 ≤ r) (i : Fin r) :
    cycleNext (cycleNext i) ≠ i := by
  intro heq
  have hv := congrArg Fin.val heq
  rw [cycleNext_val, cycleNext_val] at hv
  split_ifs at hv <;> omega

theorem cycle_edge_injective {V : Type*} {r : ℕ} (hr : 3 ≤ r)
    (f : Fin r ↪ V) : Function.Injective (fun i => s(f i, f (cycleNext i))) := by
  intro i j hij
  rcases Sym2.eq_iff.mp hij with h | h
  · exact f.injective h.1
  · have hi := f.injective h.1
    have hj := f.injective h.2
    exfalso
    apply cycleNext_two_ne hr i
    rw [hj, ← hi]

theorem cycle_copy_edgeFinset {n r : ℕ} {H : SimpleGraph (Fin n)}
    (_hr : 3 ≤ r) (f : Fin r ↪ Fin n)
    (hf : ∀ u v, H.Adj u v ↔ ∃ i j : Fin r, f i = u ∧ f j = v ∧
      ((i.val + 1) % r = j.val ∨ (j.val + 1) % r = i.val)) :
    H.edgeFinset = Finset.univ.image (fun i => s(f i, f (cycleNext i))) := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro huv
      obtain ⟨i, j, hi, hj, hstep | hstep⟩ := (hf u v).mp huv
      · have hnext : cycleNext i = j := Fin.ext hstep
        exact ⟨i, by rw [hnext, hi, hj]⟩
      · have hnext : cycleNext j = i := Fin.ext hstep
        exact ⟨j, by rw [hnext, hi, hj]; exact Sym2.eq_swap⟩
    · rintro ⟨i, hi⟩
      have hedge : H.Adj (f i) (f (cycleNext i)) :=
        (hf _ _).mpr ⟨i, cycleNext i, rfl, rfl, Or.inl rfl⟩
      have hmem : s(f i, f (cycleNext i)) ∈ H.edgeFinset :=
        SimpleGraph.mem_edgeFinset.mpr hedge
      rw [hi] at hmem
      exact SimpleGraph.mem_edgeFinset.mp hmem

theorem cycle_copy_filtered_edge_count {n r : ℕ} {H : SimpleGraph (Fin n)}
    (hr : 3 ≤ r) (f : Fin r ↪ Fin n)
    (hf : ∀ u v, H.Adj u v ↔ ∃ i j : Fin r, f i = u ∧ f j = v ∧
      ((i.val + 1) % r = j.val ∨ (j.val + 1) % r = i.val))
    (P : Sym2 (Fin n) → Prop) [DecidablePred P] :
    (H.edgeFinset.filter P).card =
      ∑ i : Fin r, if P s(f i, f (cycleNext i)) then 1 else 0 := by
  rw [cycle_copy_edgeFinset hr f hf, Finset.card_filter, Finset.sum_image]
  exact fun i hi j hj hij => cycle_edge_injective hr f hij

end Oberwolfach
