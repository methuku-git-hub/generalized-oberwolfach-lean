module

public import Oberwolfach.OrdinaryVortexAdaptiveEditBeforeSpacing
public import Oberwolfach.OrdinarySelectedCostRate

@[expose] public section
/-! The selected-cost rate is fixed before the spacing; only the finite
size threshold subsequently depends on the spacing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_selected_cost_rate_before_spacing
    (ε ρ₀ cap:ℝ) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hcap:0<cap):
    ∃rate:ℝ,0<rate ∧ ∀d:ℕ,OrdinarySelectedCostRate ε ρ₀ cap d rate :=by
  obtain ⟨rate,hrate,hgeometry⟩:=ordinary_vortex_adaptive_edit_envelope_before_spacing ε ρ₀ cap hε hε1 hρ₀ hcap
  refine ⟨rate,hrate,?_⟩
  intro d β hβ hβ1
  obtain ⟨m₀,hm₀,hgeometry⟩:=hgeometry d β hβ hβ1
  refine ⟨m₀,hm₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D mv hreg hn hhalf hρlo hρhi hm Q π hπ m pR pH βe βh b B η density tR tH s j σ rateActual hr0 hr hInner
  change OrdinaryUniformEditWeightEvents Q π hπ m d pR pH cap βe βh b B η density tR tH s j σ at hInner
  intro i hi Ledit
  have hcost:=hgeometry V U P D mv hreg hn hhalf hρlo hρhi hm Q rateActual hr0 hr i hi
  exact ⟨hcost.1,hcost.2,hInner (i+1) hi Ledit hcost.1 hcost.2⟩
end Oberwolfach
