module

public import Oberwolfach.OrdinaryCycleConflictLoss
public import Oberwolfach.OrdinaryLocalLoads

@[expose] public section

/-! Stability of the root-omitted local potential under arbitrary symmetric
changes of the spoke neighborhood. The root itself is omitted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}

theorem ordinary_local_potential_spoke_edits_loss
    (P Q F : SimpleGraph V) (T T' : Finset V)
    (φ : OrdinaryCycle P r → ℝ) (hφ : ∀ C, 0 ≤ φ C) (v : V) :
    |ordinaryLocalPotential P Q F T' φ v - ordinaryLocalPotential P Q F T φ v| ≤
      ∑ C, if v ∈ C.val.val.support ∧
        ∃ z ∈ ((T \ T') ∪ (T' \ T)), z ≠ v ∧ z ∈ C.val.val.support
        then φ C else 0 := by
  let S := (T \ T') ∪ (T' \ T)
  let base : OrdinaryCycle P r → Prop := fun C =>
    v ∈ C.val.val.support ∧ C.val.val ≤ Q ∧
      (∀ x ∈ C.val.val.support, ∀ y ∈ C.val.val.support, ¬F.Adj x y)
  let ok : Finset V → OrdinaryCycle P r → Prop := fun A C =>
    ∀ z ∈ C.val.val.support, z ≠ v → z ∈ A
  have hbad (C : OrdinaryCycle P r) (h : ok T C) (h' : ¬ok T' C) :
      ∃ z ∈ S, z ≠ v ∧ z ∈ C.val.val.support := by
    dsimp only [ok] at h h'
    push_neg at h'
    obtain ⟨z,hz,hzv,hzt⟩ := h'
    refine ⟨z, ?_, hzv, hz⟩
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h z hz hzv,hzt⟩)
  have hbad' (C : OrdinaryCycle P r) (h : ok T' C) (h' : ¬ok T C) :
      ∃ z ∈ S, z ≠ v ∧ z ∈ C.val.val.support := by
    dsimp only [ok] at h h'
    push_neg at h'
    obtain ⟨z,hz,hzv,hzt⟩ := h'
    refine ⟨z, ?_, hzv, hz⟩
    exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h z hz hzv,hzt⟩)
  have he (A : Finset V) : ordinaryLocalPotential P Q F A φ v =
      ∑ C, if base C ∧ ok A C then φ C else 0 := by
    unfold ordinaryLocalPotential
    apply Finset.sum_congr rfl
    intro C _
    dsimp only [base, ok]
    congr 1
    apply propext
    tauto
  rw [he T', he T]
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro C _
  change |(if base C ∧ ok T' C then φ C else 0) -
      (if base C ∧ ok T C then φ C else 0)| ≤
      if v ∈ C.val.val.support ∧ ∃ z ∈ S, z ≠ v ∧ z ∈ C.val.val.support
      then φ C else 0
  by_cases hb : base C
  · by_cases ht : ok T C <;> by_cases ht' : ok T' C
    · simp only [hb, ht, ht', and_self, if_true, sub_self, abs_zero]
      split_ifs <;> simp [hφ C]
    · have hx := hbad C ht ht'
      simp only [hb, ht, ht', and_true, and_false, true_and, false_and,
        ite_true, ite_false, zero_sub, sub_zero, abs_neg, abs_of_nonneg (hφ C)]
      rw [if_pos ⟨hb.1, hx⟩]
    · have hx := hbad' C ht' ht
      simp only [hb, ht, ht', and_true, and_false, true_and, false_and,
        ite_true, ite_false, zero_sub, sub_zero, abs_neg, abs_of_nonneg (hφ C)]
      rw [if_pos ⟨hb.1, hx⟩]
    · simp only [hb, ht, ht', and_false, if_false, sub_self, abs_zero]
      split_ifs <;> simp [hφ C]
  · simp only [hb, false_and, if_false, sub_self, abs_zero]
    split_ifs <;> simp [hφ C]
end Oberwolfach
