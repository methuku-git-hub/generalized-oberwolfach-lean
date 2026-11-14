module

public import Oberwolfach.OrdinarySafeCleanupScaleQuadratic

@[expose] public section
/-! A cubic deep-set error is eventually below the explicit packing tolerance
when the cleanup boundary parameters are linear in the vortex scale. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_cubic_error_below_packing_tolerance
    (r:ℕ) (p a b c cap₀ cLinear L:ℝ)
    (hp:0<p) (ha:0<a) (hb:0<b) (hc:0<c) (hcap:0<cap₀)
    (hLinear:0<cLinear) (hL:0<L):
    ∃εcap:ℝ,0<εcap ∧ εcap≤1 ∧ ∀ε:ℝ,0<ε→ε≤εcap→∀η:ℝ,
      cLinear*ordinarySafeCleanupScale r p (a*ε) (b*ε) (c*ε) (cap₀*ε^2)≤η→
      L*ε^3≤η/2 :=by
  let C:=ordinarySafeCleanupQuadraticConstant r p a b c cap₀
  have hC:0<C:=(ordinary_safe_cleanup_scale_quadratic_lower r p a b c cap₀ 0 hp ha hb hc hcap (by norm_num) (by norm_num)).1
  let εcap:=min 1 (cLinear*C/(2*L))
  have hεcap:0<εcap:=by dsimp [εcap];positivity
  refine ⟨εcap,hεcap,min_le_left _ _,?_⟩
  intro ε hε hεcap' η hη
  have hεone:ε≤1:=hεcap'.trans (min_le_left _ _)
  have hsmall:ε≤cLinear*C/(2*L):=hεcap'.trans (min_le_right _ _)
  have hcoef:2*L*ε≤cLinear*C:=by
    simpa only [mul_comm] using (le_div_iff₀ (by positivity:0<2*L)).mp hsmall
  have hscale: C*ε^2≤ordinarySafeCleanupScale r p (a*ε) (b*ε) (c*ε) (cap₀*ε^2):=
    (ordinary_safe_cleanup_scale_quadratic_lower r p a b c cap₀ ε hp ha hb hc hcap hε.le hεone).2
  have hηlow:cLinear*(C*ε^2)≤η:=(mul_le_mul_of_nonneg_left hscale hLinear.le).trans hη
  have hpoly:=mul_le_mul_of_nonneg_right hcoef (sq_nonneg ε)
  nlinarith only [hηlow,hpoly]
end Oberwolfach
