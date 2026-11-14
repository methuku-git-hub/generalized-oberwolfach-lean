module

public import Oberwolfach.OrdinarySelectedCostRate

@[expose] public section
/-! The earlier selected cost event remains valid at every smaller rate.
This permits the balance and finishing stages to use the same rate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_selected_cost_rate_mono
    (ε ρ₀ cap:ℝ) (d:ℕ) (small large:ℝ) (hle:small≤large)
    (h:OrdinarySelectedCostRate ε ρ₀ cap d large):
    OrdinarySelectedCostRate ε ρ₀ cap d small :=by
  intro β hβ hβ1
  obtain ⟨m₀,hm₀,hgood⟩:=h β hβ hβ1
  refine ⟨m₀,hm₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D mv hreg hn hhalf hρlo hρhi hm Q π hπ m pR pH βe βh b B η density tR tH s j σ rateActual hr0 hr hInner
  exact hgood V U Γ Color P D mv hreg hn hhalf hρlo hρhi hm Q π hπ m pR pH βe βh b B η density tR tH s j σ rateActual hr0 (hr.trans hle) hInner
end Oberwolfach
