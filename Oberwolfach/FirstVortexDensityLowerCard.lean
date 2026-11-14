module

public import Oberwolfach.FirstVortexDensityIdentity

@[expose] public section
/-! The actual host degree lower bound and class density lower bound supply
the parent-level lower bound on the number of factor indices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_density_lower_card
    {U:Type} [Fintype U] (n D:ℕ) (ρ₀:ℝ)
    (hD:0<D) (hρ₀:0<ρ₀) (hlo:ρ₀≤ initialIndexDensity U D)
    (hDlo:(n:ℝ)/2≤D):
    (ρ₀/8)*(n:ℝ)≤(Fintype.card U:ℝ) :=by
  have hDne:(D:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt hD)
  have hsize:initialIndexDensity U D*(D:ℝ)=2*Fintype.card U:=by
    simp [initialIndexDensity,hDne]
  have hprod:ρ₀*((n:ℝ)/2)≤ initialIndexDensity U D*(D:ℝ):=by
    calc
      ρ₀*((n:ℝ)/2)≤ρ₀*D:=mul_le_mul_of_nonneg_left hDlo hρ₀.le
      _≤ initialIndexDensity U D*(D:ℝ):=mul_le_mul_of_nonneg_right hlo (by positivity)
  have hn:(0:ℝ)≤n:=by positivity
  have hnon:0≤ρ₀*(n:ℝ):=mul_nonneg hρ₀.le hn
  nlinarith
end Oberwolfach
