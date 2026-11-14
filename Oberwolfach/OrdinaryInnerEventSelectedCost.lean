module

public import Oberwolfach.OrdinaryUniformInnerHubEvent
public import Oberwolfach.OrdinarySameSampleSelectedCostWeights

@[expose] public section
/-! The all-level inner hub event already supplies the actual selected-cost
weight events, after one deterministic rate and size choice. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_inner_event_selected_cost
    (ε ρ₀ cap:ℝ) (d:ℕ) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hcap:0<cap):
    ∃rate:ℝ,0<rate ∧ ∀β:ℝ,0≤β→β≤1/4→∃m₀:ℕ,1≤m₀ ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D mv:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀ ≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤mv→
    ∀(Q:Vortex U P D β ε mv) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (m:ℕ) (pR pH βe βh b B η:ℝ) (density tR tH:ℕ→ℝ)
      (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
      (rateActual:ℝ),0 ≤ rateActual → rateActual ≤ rate→
    OrdinaryUniformInnerHubEvent m P D mv d β ε Q π hπ pR pH βe βh b B η cap density tR tH s j σ→
    OrdinarySelectedCostWeightEvents Q π hπ m d pR pH cap βe βh b B η rateActual density tR tH s j σ :=by
  obtain ⟨rate,hrate,hcost⟩:=ordinary_vortex_uniform_edit_cost_events ε ρ₀ cap d hε hε1 hρ₀ hcap
  refine ⟨rate,hrate,?_⟩
  intro β hβ hβ1
  obtain ⟨m₀,hm₀,hcost⟩:=hcost β hβ hβ1
  refine ⟨m₀,hm₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D mv hreg hn hhalf hρlo hρhi hm Q π hπ m pR pH βe βh b B η density tR tH s j raw
    rateActual hr0 hr hInner
  exact hcost V U Γ Color P D mv hreg hn hhalf hρlo hρhi hm Q π hπ m pR pH βe βh b B η density tR tH s j raw
    rateActual hr0 hr hInner
end Oberwolfach
