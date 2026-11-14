module

public import Oberwolfach.FourBarrierDeletion
public import Oberwolfach.ThresholdBounds

@[expose] public section

/-! Divisible counterexamples establish the ordinary four-cycle threshold bound.
The graphs here have even degrees, but are not asserted to be regular. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem four_barrier_choose_odd (k : ℕ) : Odd ((4 * k + 7).choose 2) := by
  have hh : 2 * (4 * k + 7).choose 2 = (4 * k + 7) * (4 * k + 6) := by
    rw [Nat.choose_two_right,
      Nat.mul_div_cancel' (Nat.even_mul_pred_self (4 * k + 7)).two_dvd]
    congr 1
  refine ⟨4 * k ^ 2 + 13 * k + 10, ?_⟩
  nlinarith

theorem four_barrier_edge_divisible (k : ℕ) :
    4 ∣ 3 * (4 * k + 7) * (4 * k + 6) - 6 := by
  refine ⟨12 * k ^ 2 + 39 * k + 30, ?_⟩
  have hh : 3 * (4 * k + 7) * (4 * k + 6) =
      4 * (12 * k ^ 2 + 39 * k + 30) + 6 := by ring
  omega

theorem four_threshold_counterexample {d : ℝ} (hd : d < 2 / 3) (N : ℕ) :
    ∃ n ≥ N, ∃ G : SimpleGraph (Fin n), CycleDivisible G 4 ∧
      (∀ v, d * (n : ℝ) ≤ (G.degree v : ℝ)) ∧ ¬ HasCycleDecomposition G 4 := by
  have hm : 0 < 2 - 3 * d := by linarith
  let k := max (N + 1) ⌈(4 + |d|) / (2 - 3 * d)⌉₊
  let t := 4 * k + 7
  have ht : 6 ≤ t := by dsimp only [t]; omega
  have hkN : N + 1 ≤ k := le_max_left _ _
  have hkt : k ≤ t := by dsimp only [t]; omega
  have hceil : (4 + |d|) / (2 - 3 * d) ≤ (t : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast
      (show ⌈(4 + |d|) / (2 - 3 * d)⌉₊ ≤ t from (le_max_right _ _).trans hkt))
  have hmargin := (div_le_iff₀ hm).mp hceil
  refine ⟨(t + t) + (t - 1), by omega, fourBarrierGraph ht, ?_, ?_, ?_⟩
  · constructor
    · intro v
      exact (fourBarrierGraph_degrees ht v).1
    · rw [fourBarrierGraph_edge_card]
      have heq : t - 1 = 4 * k + 6 := by dsimp only [t]; omega
      rw [heq]
      exact four_barrier_edge_divisible k
  · intro v
    have hdeg := (fourBarrierGraph_degrees ht v).2
    have hdeg' : (2 : ℝ) * t - 4 ≤ (fourBarrierGraph ht).degree v := by
      have hh : ((2 * t - 4 : ℕ) : ℝ) ≤ (fourBarrierGraph ht).degree v := by exact_mod_cast hdeg
      simpa only [Nat.cast_sub (by omega : 4 ≤ 2 * t), Nat.cast_mul, Nat.cast_ofNat] using hh
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ t), Nat.cast_one]
    nlinarith [neg_le_abs d]
  · exact fourBarrierGraph_no_decomposition ht (four_barrier_choose_odd k)

theorem cycleThreshold_four_lower : (2 / 3 : ℝ) ≤ cycleThreshold 4 := by
  apply le_csInf (show {d | AdmissibleCycleBound 4 d}.Nonempty from ⟨1, one_admissible 4⟩)
  intro d hd
  by_contra hnot
  obtain ⟨N, hN⟩ := hd.2
  obtain ⟨n, hn, G, hdiv, hdegree, hno⟩ :=
    four_threshold_counterexample (lt_of_not_ge hnot) N
  exact hno (hN n hn G hdiv hdegree)

end Oberwolfach
