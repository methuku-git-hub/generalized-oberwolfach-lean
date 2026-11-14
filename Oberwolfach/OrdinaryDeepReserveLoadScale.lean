module

public import Oberwolfach.OrdinarySafeCleanupScaleQuadratic

@[expose] public section
/-! A cover-load rate proportional to the square of the vortex scale fits
the later quantitative geometry budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_reserve_quadratic_load_scale
    (r m:ℕ) (p a b c cap₀ cLinear cGeom:ℝ)
    (hp:0<p) (ha:0<a) (hb:0<b) (hc:0<c) (hcap:0<cap₀)
    (hLinear:0<cLinear) (hGeom:0<cGeom):
    ∃cLoad:ℝ,0<cLoad ∧ cLoad≤1 ∧ ∀ε:ℝ,0<ε→ε≤1→∀η γ:ℝ,
      cLinear*ordinarySafeCleanupScale r p (a*ε) (b*ε) (c*ε) (cap₀*ε^2)≤η→
      cGeom*min 1 η≤γ→
      0<cLoad*ε^2 ∧ cLoad*ε^2≤1 ∧ cLoad*ε^2≤γ/(1000*((m:ℝ)+2)) :=by
  let C:=ordinarySafeCleanupQuadraticConstant r p a b c cap₀
  have hC:0<C:=(ordinary_safe_cleanup_scale_quadratic_lower r p a b c cap₀ 0 hp ha hb hc hcap (by norm_num) (by norm_num)).1
  let K:ℝ:=1000*((m:ℝ)+2)
  have hK:0<K:=by dsimp [K];positivity
  let cLower:ℝ:=min 1 (cLinear*C)
  have hLower:0<cLower:=by dsimp [cLower];positivity
  let cLoad:ℝ:=min (1/2) (cGeom*cLower/(2*K))
  have hLoad:0<cLoad:=by dsimp [cLoad];positivity
  have hLoad1:cLoad≤1:=by have hh:=min_le_left (1/2:ℝ) (cGeom*cLower/(2*K));dsimp [cLoad];linarith
  have hLoadK:cLoad*K≤cGeom*cLower/2:=by
    have hh:=min_le_right (1/2:ℝ) (cGeom*cLower/(2*K))
    have hk:=mul_le_mul_of_nonneg_right hh hK.le
    have heq:(cGeom*cLower/(2*K))*K=cGeom*cLower/2:=by field_simp
    rw [heq] at hk
    exact hk
  refine ⟨cLoad,hLoad,hLoad1,?_⟩
  intro ε hε hε1 η γ hη hγ
  have hsq0:0≤ε^2:=sq_nonneg ε
  have hsq1:ε^2≤1:=by nlinarith [sq_nonneg (1-ε)]
  have hscale:C*ε^2≤ordinarySafeCleanupScale r p (a*ε) (b*ε) (c*ε) (cap₀*ε^2):=
    (ordinary_safe_cleanup_scale_quadratic_lower r p a b c cap₀ ε hp ha hb hc hcap hε.le hε1).2
  have hlowerη:cLower*ε^2≤η:=by
    have hc:=min_le_right (1:ℝ) (cLinear*C)
    have hh:=mul_le_mul_of_nonneg_right hc hsq0
    have hh':=mul_le_mul_of_nonneg_left hscale hLinear.le
    nlinarith only [hh,hh',hη]
  have hlower1:cLower*ε^2≤1:=by
    have hc:=min_le_left (1:ℝ) (cLinear*C)
    nlinarith [mul_nonneg hLower.le (sub_nonneg.mpr hsq1)]
  have hlower:cLower*ε^2≤min 1 η:=le_min hlower1 hlowerη
  have hγlower:cGeom*(cLower*ε^2)≤γ:=
    (mul_le_mul_of_nonneg_left hlower hGeom.le).trans hγ
  refine ⟨by positivity,?_,?_⟩
  · nlinarith [mul_nonneg hLoad.le (sub_nonneg.mpr hsq1)]
  · apply (le_div_iff₀ hK).2
    have hh:=mul_le_mul_of_nonneg_right hLoadK hsq0
    have hnon:0≤cGeom*cLower*ε^2:=by positivity
    dsimp [K] at *
    nlinarith only [hh,hγlower,hnon]
end Oberwolfach
