module

public import Oberwolfach.LongAssignmentUniformTolerances

@[expose] public section
/-! A smaller fixed hub-count tolerance suffices simultaneously for the
ordinary assignment and the manuscript's sharp test-mass estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach

theorem long_assignment_manuscript_tolerances_exist
    (t₀ τ₀ Δ₀ C eps:ℝ) (ht₀:0<t₀) (hτ₀:0<τ₀) (hΔ₀:0<Δ₀) (hC:0≤C) (heps:0<eps):
    ∃t₁ τ₁ Δ₁ ξ:ℝ,0<t₁ ∧ t₁≤t₀ ∧ 0<τ₁ ∧ τ₁≤τ₀ ∧ 0<Δ₁ ∧ Δ₁≤Δ₀ ∧
      0<ξ ∧ ξ≤1/128 ∧ 4*ξ≤eps/2 ∧
      ∀t τ x:ℝ,0≤t→t≤t₁→0≤τ→τ≤τ₁→0≤x→x≤Δ₁→
        0≤t+C*x+4*τ ∧ t+C*x+4*τ≤eps/2 :=by
  obtain ⟨t₁,τ₁,Δ₁,ξ₀,ht,htle,hτ,hτle,hΔ,hΔle,hξ,_,hξeps,herror⟩:=
    long_assignment_uniform_tolerances_exist t₀ τ₀ Δ₀ C eps ht₀ hτ₀ hΔ₀ hC heps
  let ξ:=min ξ₀ (1/128:ℝ)
  have hξpos:0<ξ:=lt_min hξ (by norm_num)
  have hξ0:ξ≤ξ₀:=min_le_left _ _
  have hξbound:ξ≤1/128:=min_le_right _ _
  have hξeps':4*ξ≤eps/2:=by linarith
  exact ⟨t₁,τ₁,Δ₁,ξ,ht,htle,hτ,hτle,hΔ,hΔle,hξpos,hξbound,hξeps',herror⟩
end Oberwolfach
