module

public import Oberwolfach.AsymptoticMargins
public import Oberwolfach.DivisibilityRepairScales

@[expose] public section

/-! The vertex sample size is fixed before the host graph and the supplied
edge vector. Its failure probability is small relative to the positive baseline. -/
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace Oberwolfach

theorem ordinary_positive_sample_size (N₀ : ℕ) (α κ : ℝ) (hα : 0<α) (hκ : 0<κ) :
    ∃ m : ℕ,N₀≤m ∧ 4≤m ∧ 3≤α*m/4 ∧
      8*m*Real.exp (-α^2*m/32)<κ/4 := by
  have hc : 0<α^2/32 := by positivity
  have ht := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) (α^2/32) hc).const_mul 8).comp
    tendsto_natCast_atTop_atTop
  have ht' : Tendsto (fun n : ℕ => 8*n*Real.exp (-α^2*n/32)) atTop (𝓝 0) := by
    convert ht using 1
    · funext n
      dsimp only [Function.comp_apply]
      rw [Real.rpow_one]
      have he : -(α^2/32)*(n:ℝ)=-α^2*n/32 := by ring
      rw [he]
      ring
    · norm_num
  have hb : ∀ᶠ n : ℕ in atTop,8*n*Real.exp (-α^2*n/32)<κ/4 :=
    ht'.eventually (eventually_lt_nhds (show (0:ℝ)<κ/4 by positivity))
  obtain ⟨N₁,h₁⟩ := eventually_atTop.mp hb
  obtain ⟨N₂,h₂⟩ := eventually_constant_le_linear 3 (α/4) (by positivity)
  refine ⟨max (max N₀ 4) (max N₁ N₂),by omega,by omega,?_,h₁ _ (by omega)⟩
  have hh := h₂ (max (max N₀ 4) (max N₁ N₂)) (by omega)
  linarith only [hh]

end Oberwolfach
