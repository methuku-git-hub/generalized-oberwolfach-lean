module

public import Oberwolfach.OrdinaryLocalPotentialSpokeEdits
public import Oberwolfach.OrdinaryCyclePairWeight

@[expose] public section

/-! Quantitative bound for a root-omitted spoke-neighborhood edit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}

theorem ordinary_local_potential_spoke_edits_bound
    (P Q F : SimpleGraph V) (T T' : Finset V)
    (hr : 2 ≤ r) (hn : 0 < Fintype.card V)
    (φ : OrdinaryCycle P r → ℝ) (hφ : ∀ C, 0 ≤ φ C)
    (B L : ℝ) (hB : 0 ≤ B)
    (hφB : ∀ C, φ C ≤ B / (Fintype.card V : ℝ) ^ (r - 1))
    (hL : (((T \ T') ∪ (T' \ T)).card : ℝ) ≤ L) (v : V) :
    |ordinaryLocalPotential P Q F T' φ v - ordinaryLocalPotential P Q F T φ v| ≤
      (r : ℝ)^2 * B * L / Fintype.card V := by
  let S := (T \ T') ∪ (T' \ T)
  have hnR : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr hn
  have hc : ∀ C, φ C ≤ (B / Fintype.card V) / (Fintype.card V : ℝ) ^ (r - 2) := by
    intro C
    have he : (B / Fintype.card V) / (Fintype.card V : ℝ) ^ (r - 2) =
        B / (Fintype.card V : ℝ) ^ (r - 1) := by
      rw [div_div, ← pow_succ', show r - 2 + 1 = r - 1 by omega]
    rw [he]
    exact hφB C
  have hp (z : V) (hz : z ≠ v) :
      (∑ C, if v ∈ C.val.val.support ∧ z ∈ C.val.val.support then φ C else 0) ≤
        (r : ℝ)^2 * (B / Fintype.card V) := by
    convert ordinary_cycle_pair_weight_bound P r v z hz.symm hn (B / Fintype.card V)
      (div_nonneg hB hnR.le) φ hc using 1 <;> congr!
  have hu : (∑ C, if v ∈ C.val.val.support ∧
      ∃ z, z ∈ S ∧ z ≠ v ∧ z ∈ C.val.val.support then φ C else 0) ≤
      ∑ z : V, ∑ C, if v ∈ C.val.val.support ∧
        (z ∈ S ∧ z ≠ v ∧ z ∈ C.val.val.support) then φ C else 0 := by
    convert finite_weighted_union_bound φ hφ (fun C => v ∈ C.val.val.support)
      (fun C z => z ∈ S ∧ z ≠ v ∧ z ∈ C.val.val.support) using 1 <;> congr!
  have hs : (∑ z : V, ∑ C, if v ∈ C.val.val.support ∧
      (z ∈ S ∧ z ≠ v ∧ z ∈ C.val.val.support) then φ C else 0) ≤
      (S.card : ℝ) * ((r : ℝ)^2 * (B / Fintype.card V)) := by
    calc
      _ ≤ ∑ z : V, if z ∈ S then (r : ℝ)^2 * (B / Fintype.card V) else 0 := by
        apply Finset.sum_le_sum
        intro z _
        by_cases hzs : z ∈ S
        · rw [if_pos hzs]
          by_cases hz : z = v
          · subst z
            simp only [ne_eq, not_true_eq_false, false_and, and_false, ite_false, Finset.sum_const_zero]
            positivity
          · have he : (∑ C, if v ∈ C.val.val.support ∧
                (z ∈ S ∧ z ≠ v ∧ z ∈ C.val.val.support) then φ C else 0) =
                ∑ C, if v ∈ C.val.val.support ∧ z ∈ C.val.val.support then φ C else 0 := by
              apply Finset.sum_congr rfl
              intro C _
              have hc : (v ∈ C.val.val.support ∧
                  (z ∈ S ∧ z ≠ v ∧ z ∈ C.val.val.support)) ↔
                  (v ∈ C.val.val.support ∧ z ∈ C.val.val.support) := by
                constructor
                · intro h; exact ⟨h.1,h.2.2.2⟩
                · intro h; exact ⟨h.1,hzs,hz,h.2⟩
              exact if_congr hc rfl rfl
            rw [he]
            exact hp z hz
        · simp only [hzs, false_and, and_false, ite_false, Finset.sum_const_zero, le_refl]
      _ = _ := by simp
  have hstart := ordinary_local_potential_spoke_edits_loss P Q F T T' φ hφ v
  have hh : |ordinaryLocalPotential P Q F T' φ v - ordinaryLocalPotential P Q F T φ v| ≤
      (S.card : ℝ) * ((r : ℝ)^2 * (B / Fintype.card V)) := by
    apply hstart.trans
    convert hu.trans hs using 1 <;> congr!
  calc
    _ ≤ (S.card : ℝ) * ((r : ℝ)^2 * (B / Fintype.card V)) := hh
    _ ≤ L * ((r : ℝ)^2 * (B / Fintype.card V)) := by
      apply mul_le_mul_of_nonneg_right hL
      positivity
    _ = _ := by ring
end Oberwolfach
