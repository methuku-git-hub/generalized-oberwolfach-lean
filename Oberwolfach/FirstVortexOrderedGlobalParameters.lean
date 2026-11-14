module

public import Oberwolfach.FirstVortexDensityGlobalTolerance
public import Oberwolfach.FirstVortexResidualMatchingAlphaChoice

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_ordered_global_parameters
    (αold b ρ₀ C₀ θ δ:ℝ) (d K:ℕ)
    (hαold:0<αold) (hρ₀:0<ρ₀) (hC:1≤C₀) (hθ:0<θ) (hδ:0<δ)
    (hd:0<d) (hK:0<K) (hαb:αold/16≤b):
    ∃α:ℝ,0<α ∧ α≤αold ∧ α≤δ ∧ α/16≤b ∧ α/16≤((ρ₀/4)/40000)*θ/1024 ∧
    ∃ε:ℝ,0<ε ∧ ε≤δ ∧ ε≤1/100 ∧ ε≤α/(1000*C₀) ∧ ε≤(ρ₀/4)/80000 ∧
    ∀lam:ℝ,0<lam→
      ∃ρ eps a γ:ℝ,0<ρ ∧ ρ≤θ/4096 ∧
        0<eps ∧ eps≤1 ∧ 3*eps≤lam*(θ/(100*(K:ℝ)^2)) ∧
        0<a ∧ a≤lam/(10*d) ∧ a≤θ/(200*(K:ℝ)^2) ∧
        0<γ ∧ γ≤eps ∧ γ≤eps/2 ∧ γ≤1/2 ∧ γ≤lam/(10*d) ∧ γ≤lam/10 ∧
        ∀(V U:Type) [Fintype V] [Fintype U] (G:SimpleGraph V) (D m:ℕ) (β:ℝ)
          (Q:Vortex U G D β ε m),0<m→
          max a γ*(Fintype.card V:ℝ)≤ρ*(Q.extendedVertices 1).card ∧
          2*(max a γ*(Fintype.card V:ℝ))≤δ*(Q.extendedVertices 1).card/4 :=by
  obtain ⟨α₀,hα₀,hα₀le,hα₀b,hα₀small⟩:=first_vortex_residual_matching_alpha_choice αold b ρ₀ θ hαold hρ₀ hθ hαb
  let α:=min α₀ δ
  have hα:0<α:=lt_min hα₀ hδ
  have hαle:α≤α₀:=min_le_left _ _
  have hαδ:α≤δ:=min_le_right _ _
  have hαb':α/16≤b:=by linarith
  have hαsmall:α/16≤((ρ₀/4)/40000)*θ/1024:=by linarith
  obtain ⟨ε,hε,hεδ,hε1,hεα,hερ,hRates⟩:=first_vortex_event_density_and_matching_rates_with_global_tolerance α ρ₀ C₀ θ δ d K hα hρ₀ hC hθ hδ hd hK
  exact ⟨α,hα,le_trans hαle hα₀le,hαδ,hαb',hαsmall,ε,hε,hεδ,hε1,hεα,hερ,hRates⟩
end Oberwolfach
