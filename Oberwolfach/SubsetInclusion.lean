module

public import Oberwolfach.SubsetCounts
public import Oberwolfach.ChooseRatio

@[expose] public section

/-! Joint inclusion probabilities, with the fixed-cardinality law retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem fixedSubset_joint_inclusion {V : Type*} [Fintype V] {r : ℕ}
    [Nonempty (FixedSubset V r)] (hr : r ≤ Fintype.card V) (T : Finset V) :
    (FiniteLaw.uniform (FixedSubset V r)).probability (fun S => T ⊆ S.1) =
      (r.choose T.card : ℝ) / (Fintype.card V).choose T.card := by
  by_cases hk : T.card ≤ r
  · rw [fixedSubset_inclusion_probability T hk]
    have hrpos : ((Fintype.card V).choose r : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hr).ne'
    have hkpos : ((Fintype.card V).choose T.card : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos T.card_le_univ).ne'
    apply (div_eq_div_iff hrpos hkpos).mpr
    have hh := Nat.choose_mul (n := Fintype.card V) hk
    exact_mod_cast (by nlinarith [hh] :
      (Fintype.card V - T.card).choose (r - T.card) * (Fintype.card V).choose T.card =
        r.choose T.card * (Fintype.card V).choose r)
  · have hzero : r.choose T.card = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hzero, Nat.cast_zero, zero_div]
    unfold FiniteLaw.probability
    apply Finset.sum_eq_zero
    intro S _
    have hn : ¬ T ⊆ S.1 := by
      intro hh
      have hc := Finset.card_le_card hh
      rw [S.2] at hc
      exact hk hc
    simp [hn]

theorem fixedSubset_joint_inclusion_le {V : Type*} [Fintype V] {r : ℕ}
    [Nonempty (FixedSubset V r)] (hr : r ≤ Fintype.card V) (T : Finset V) :
    (FiniteLaw.uniform (FixedSubset V r)).probability (fun S => T ⊆ S.1) ≤
      ((r : ℝ) / Fintype.card V) ^ T.card := by
  rw [fixedSubset_joint_inclusion hr T]
  exact choose_ratio_le_power hr T.card_le_univ

end Oberwolfach
