module

public import Oberwolfach.LongPreparationPhysicalFeasible

@[expose] public section
/-! The selected marked-state density is the selected ordinary-state density
divided by the number of ordinary positions, as required by the reference law. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_preparation_selected_density_identity (ρ s₀:ℝ) (m:ℕ) (hm:0<m):
    ρ*(s₀/(m:ℝ))/2=(ρ*s₀/2)/(m:ℝ):=by ring
end Oberwolfach
