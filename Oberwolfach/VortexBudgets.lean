module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic

@[expose] public section

/-! One parameter threshold supplies the degree and rounding margins at all later sizes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
noncomputable section
namespace Oberwolfach

theorem eventually_vortex_error_budget {β ε ρ : ℝ}
    (hb : 0 < β) (he : 0 < ε) (he1 : ε < 1) (hp : 0 < ρ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ m : ℕ, N ≤ m →
      2 ≤ ε * m ∧
      (m : ℝ) ^ (-1 / 3 : ℝ) / (1 - ε ^ (1 / 3 : ℝ)) ≤ β / 2 ∧
      3 / ρ ≤ β * ε * m / 4 := by
  have hq : ε ^ (1 / 3 : ℝ) < 1 := by
    have hh := Real.rpow_lt_rpow he.le he1 (by norm_num : (0 : ℝ) < 1 / 3)
    simpa using hh
  have hden : 0 < 1 - ε ^ (1 / 3 : ℝ) := by linarith
  have ht := (tendsto_rpow_neg_atTop (y := (1 / 3 : ℝ)) (by norm_num)).comp
    tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ m : ℕ in atTop, (m : ℝ) ^ (-1 / 3 : ℝ) <
      β / 2 * (1 - ε ^ (1 / 3 : ℝ)) := by
    simpa only [neg_div, Function.comp_apply] using ht.eventually
      (eventually_lt_nhds (show 0 < β / 2 * (1 - ε ^ (1 / 3 : ℝ)) by positivity))
  obtain ⟨N₁, h₁⟩ := eventually_atTop.mp hevent
  refine ⟨max 1 (max N₁ (max (Nat.ceil (2 / ε)) (Nat.ceil (12 / (ρ * β * ε))))), le_max_left _ _, ?_⟩
  intro m hm
  have hm1 := h₁ m (by omega)
  have hm2 : 2 ≤ ε * m := by
    have hh : (Nat.ceil (2 / ε) : ℝ) ≤ m := by
      exact_mod_cast (show Nat.ceil (2 / ε) ≤ m by omega)
    have hdiv := (div_le_iff₀ he).mp ((Nat.le_ceil (2 / ε)).trans hh)
    nlinarith
  have hceil : (Nat.ceil (12 / (ρ * β * ε)) : ℝ) ≤ m := by
    exact_mod_cast (show Nat.ceil (12 / (ρ * β * ε)) ≤ m by omega)
  have hm3 := (Nat.le_ceil (12 / (ρ * β * ε))).trans hceil
  refine ⟨hm2, (div_le_iff₀ hden).mpr hm1.le, ?_⟩
  have hprod : 0 < ρ * β * ε := by positivity
  have hh := (div_le_iff₀ hprod).mp hm3
  apply (div_le_iff₀ hp).mpr
  nlinarith

end Oberwolfach
