module

public import Oberwolfach.Definitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

/-- Degree at least n is impossible in a nonempty n-vertex simple graph.
Thus 1 belongs to the set whose infimum defines the cycle threshold. -/
theorem one_admissible (r : ℕ) : AdmissibleCycleBound r 1 := by
  classical
  refine ⟨by norm_num, 1, ?_⟩
  intro n hn G hdiv hdeg
  let v : Fin n := ⟨0, by omega⟩
  have hlt : G.degree v < n := by simpa using G.degree_lt_card_verts v
  have hge := hdeg v
  simp only [one_mul] at hge
  have hlt' : (G.degree v : ℝ) < n := by exact_mod_cast hlt
  exact False.elim (not_lt_of_ge hge hlt')

theorem cycleThreshold_nonneg (r : ℕ) : 0 ≤ cycleThreshold r := by
  apply le_csInf (show {d | AdmissibleCycleBound r d}.Nonempty from ⟨1, one_admissible r⟩)
  intro d hd
  exact hd.1.1

theorem cycleThreshold_le_one (r : ℕ) : cycleThreshold r ≤ 1 := by
  apply csInf_le (show BddBelow {d | AdmissibleCycleBound r d} from ?_) (one_admissible r)
  refine ⟨0, ?_⟩
  intro d hd
  exact hd.1.1

/-- The definition of the infimum really implies the positive-margin statement. -/
theorem cycleThreshold_positive_margin (r : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), CycleDivisible G r →
      (∀ v, (cycleThreshold r + α) * (n : ℝ) ≤ (G.degree v : ℝ)) →
      HasCycleDecomposition G r := by
  classical
  have hn : {d | AdmissibleCycleBound r d}.Nonempty := ⟨1, one_admissible r⟩
  obtain ⟨d, hd, hdlt⟩ := exists_lt_of_csInf_lt hn (show cycleThreshold r < cycleThreshold r + α by linarith)
  obtain ⟨N, hN⟩ := hd.2
  refine ⟨N, ?_⟩
  intro n hn G hdiv hdeg
  apply hN n hn G hdiv
  intro v
  exact (mul_le_mul_of_nonneg_right hdlt.le (Nat.cast_nonneg n)).trans (hdeg v)

end Oberwolfach
