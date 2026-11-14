module

public import Oberwolfach.FirstVortexDensityIdentity

@[expose] public section
/-! The original degree and density hypotheses give the exact parent-index
lower bound used in the selected correction cap. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_density_parent_lower_card
    {U:Type} [Fintype U] (n D:ℕ) (ρ₀:ℝ)
    (hD:0<D) (hρ₀:0<ρ₀) (hlo:ρ₀≤ initialIndexDensity U D)
    (hDlo:(n:ℝ)/2≤D):
    (ρ₀/4)*(n:ℝ)≤(Fintype.card U:ℝ) :=by
  have hDne:(D:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt hD)
  have hsize:initialIndexDensity U D*(D:ℝ)=2*Fintype.card U:=by
    simp [initialIndexDensity,hDne]
  have hprod:ρ₀*((n:ℝ)/2)≤ initialIndexDensity U D*(D:ℝ):=by
    calc
      ρ₀*((n:ℝ)/2)≤ρ₀*D:=mul_le_mul_of_nonneg_left hDlo hρ₀.le
      _≤ initialIndexDensity U D*(D:ℝ):=mul_le_mul_of_nonneg_right hlo (by positivity)
  nlinarith
end Oberwolfach
