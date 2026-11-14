module

public import Oberwolfach.FirstVortexPrescribedHubDensity
public import Oberwolfach.FirstVortexHubCardinality

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_host_hub_cardinality_bounds
    {n D:ℕ} {U:Type} [Fintype U] {G:SimpleGraph (Fin n)}
    (hreg:G.IsRegularOfDegree D) (hn:0<n) (hD:(n:ℝ)/2≤D)
    (ρ₀:ℝ) (hρ₀:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D)
    (hρhi:initialIndexDensity U D≤1):
    0<Fintype.card U ∧ Fintype.card U≤n :=by
  have hnR:(0:ℝ)<n:=by exact_mod_cast hn
  have hDposR:(0:ℝ)<D:=by linarith
  have hDpos:0<D:=by exact_mod_cast hDposR
  have hmass:0<ρ₀/4 ∧ (ρ₀/4)*n≤Fintype.card U:=
    first_vortex_prescribed_hub_density hreg hn hD ρ₀ hρ₀ hρlo
  have hUposR:(0:ℝ)<Fintype.card U:=lt_of_lt_of_le (mul_pos hmass.1 hnR) hmass.2
  have hUpos:0<Fintype.card U:=by exact_mod_cast hUposR
  exact ⟨hUpos,first_vortex_hub_cardinality_le_host hreg hn hDpos hρhi⟩
end Oberwolfach
