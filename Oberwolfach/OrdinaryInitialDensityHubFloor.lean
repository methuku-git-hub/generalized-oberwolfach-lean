module

public import Oberwolfach.OrdinaryAssignedReferenceOriginalInputs

@[expose] public section
/-! The original host degree and index-density hypotheses give a common
linear lower bound on the number of hubs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_initial_density_hub_floor
    {n D:ℕ} {U:Type} [Fintype U]
    (ρ₀:ℝ) (hρ₀:0<ρ₀) (hD:0<D) (hDlo:(n:ℝ)/2≤D)
    (hρ:ρ₀≤ initialIndexDensity U D):
    (ρ₀/4)*(n:ℝ)≤Fintype.card U :=by
  have hDreal:0<(D:ℝ):=by exact_mod_cast hD
  have hsize:initialIndexDensity U D*(D:ℝ)=2*(Fintype.card U:ℝ):=by
    simp [initialIndexDensity,ne_of_gt hDreal]
  have h1:=mul_le_mul_of_nonneg_right hρ hDreal.le
  have h2:=mul_le_mul_of_nonneg_left hDlo hρ₀.le
  nlinarith only [h1,h2,hsize]
end Oberwolfach
