module

public import Oberwolfach.NormalizedCycleWeightBounds

@[expose] public section
/-! Fixed lower and upper bounds for the two-hub density product. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
theorem pair_hub_density_bounds (r:ℕ) (p pmin s₁ s₂ smin:ℝ)
    (hpmin:0<pmin) (hp:pmin≤p) (hp1:p≤1)
    (hsmin:0<smin) (hs₁:smin≤s₁) (hs₂:smin≤s₂) (hs₁1:s₁≤1) (hs₂1:s₂≤1):
    0<pmin^r*(smin*smin)^(r-1) ∧
      pmin^r*(smin*smin)^(r-1)≤p^r*(s₁*s₂)^(r-1) ∧
      p^r*(s₁*s₂)^(r-1)≤1 := by
  have hp0:0≤p:=le_trans hpmin.le hp
  have hs10:0≤s₁:=le_trans hsmin.le hs₁
  have hs20:0≤s₂:=le_trans hsmin.le hs₂
  have hsm:0≤smin*smin:=mul_nonneg hsmin.le hsmin.le
  have hsprod:smin*smin≤s₁*s₂:=mul_le_mul hs₁ hs₂ hsmin.le hs10
  have hsprod1:s₁*s₂≤1:=by nlinarith [mul_nonneg hs10 (sub_nonneg.mpr hs₂1)]
  constructor
  · positivity
  constructor
  · exact mul_le_mul (pow_le_pow_left₀ hpmin.le hp _) (pow_le_pow_left₀ hsm hsprod _) (pow_nonneg hsm _) (pow_nonneg hp0 _)
  · have hpbound:p^r≤1:=by simpa using pow_le_one₀ hp0 hp1
    have hsbound:(s₁*s₂)^(r-1)≤1:=by simpa using pow_le_one₀ (mul_nonneg hs10 hs20) hsprod1
    nlinarith [mul_nonneg (pow_nonneg hp0 r) (sub_nonneg.mpr hsbound)]
end Oberwolfach
