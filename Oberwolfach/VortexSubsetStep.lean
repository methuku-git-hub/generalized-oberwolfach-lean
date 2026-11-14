module

public import Oberwolfach.NormalizedSubsetCounts
public import Oberwolfach.VortexStepMargins

@[expose] public section

/-! The uniform subset selection step, uniformly over all fixed external tests. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
universe u v

theorem vortex_uniform_subset_step {ε : ℝ} (he : 0 < ε) (he1 : ε ≤ 1) :
    ∃ N : ℕ, ∀ (V : Type u) [Fintype V], N ≤ Fintype.card V →
      ∀ (J : Type v) (tests : Finset J) (A : J → Finset V),
      (tests.card : ℝ) ≤ 2 * Fintype.card V / ε →
      ∃ S : FixedSubset V (Nat.floor (ε * Fintype.card V)), ∀ j ∈ tests,
        |((A j ∩ S.1).card : ℝ) / (Nat.floor (ε * Fintype.card V) : ℕ) -
          ((A j).card : ℝ) / Fintype.card V| <
          (Fintype.card V : ℝ) ^ (-1 / 3 : ℝ) := by
  obtain ⟨N, hN⟩ := eventually_vortex_step_margins he
  refine ⟨N, ?_⟩
  intro V _ hn J tests A htests
  obtain ⟨hn2, hlarge, hsmall⟩ := hN (Fintype.card V) hn
  obtain ⟨hrpos, hr, hrlo⟩ := vortex_floor_step_bounds he1 hlarge
  apply fixedSubset_normalized_counts_exists hr hrpos tests A (by positivity)
  have hexp := vortex_normalized_exponent (by omega : 0 < Fintype.card V) hrlo
  have hcoef : 2 * (tests.card : ℝ) ≤ 4 * Fintype.card V / ε := by
    calc
      _ ≤ 2 * (2 * Fintype.card V / ε) := mul_le_mul_of_nonneg_left htests (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ (4 * Fintype.card V / ε) *
        Real.exp (-ε * (Fintype.card V : ℝ) ^ (1 / 3 : ℝ)) :=
      mul_le_mul hcoef (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by positivity)
    _ < 1 := hsmall

end Oberwolfach
