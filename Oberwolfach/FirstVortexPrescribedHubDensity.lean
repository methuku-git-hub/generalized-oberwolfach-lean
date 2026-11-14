module

public import Oberwolfach.MarkedVortexDensityMass

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_prescribed_hub_density
    {n D:ℕ} {U:Type} [Fintype U] {G:SimpleGraph (Fin n)}
    (hreg:G.IsRegularOfDegree D) (hn:0<n) (hD:(n:ℝ)/2≤D)
    (ρ₀:ℝ) (hρ₀:0<ρ₀) (hrlo:ρ₀ ≤ initialIndexDensity U D):
    0<ρ₀/4 ∧ (ρ₀/4)*n≤Fintype.card U:=by
  have hh:=marked_vortex_hub_mass_lower hreg (by simpa using hn) (by simpa using hD) ρ₀ hρ₀ hrlo
  constructor
  · positivity
  · simpa only [Fintype.card_fin] using (by nlinarith only [hh] : (ρ₀/4)*(Fintype.card (Fin n):ℝ)≤Fintype.card U)
end Oberwolfach
