module

public import Oberwolfach.OrdinaryDeepCubicTolerance

@[expose] public section
/-! The cubic reserve fits a geometry tolerance bounded below by a fixed
multiple of the clipped packing tolerance, for sufficiently small vortex scale. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_reserve_below_quantitative_geometry
    (r:ℕ) (p a b c cap₀ cLinear cGeom K:ℝ)
    (hp:0<p) (ha:0<a) (hb:0<b) (hc:0<c) (hcap:0<cap₀)
    (hLinear:0<cLinear) (hGeom:0<cGeom) (hK:0<K):
    ∃εcap:ℝ,0<εcap ∧ εcap≤1 ∧ ∀ε:ℝ,0<ε→ε≤εcap→∀η γ:ℝ,
      cLinear*ordinarySafeCleanupScale r p (a*ε) (b*ε) (c*ε) (cap₀*ε^2)≤η→
      cGeom*min 1 η≤γ→2*ε^3≤γ/K :=by
  let c':ℝ:=cLinear*cGeom/K
  have hc':0<c':=by dsimp [c'];positivity
  obtain ⟨e₀,he₀,he₀one,hsmall⟩:=ordinary_deep_cubic_error_below_packing_tolerance r p a b c cap₀ c' 2
    hp ha hb hc hcap hc' (by norm_num)
  let εcap:ℝ:=min e₀ (1/(1+cLinear*cap₀))
  have hεcap:0<εcap:=by dsimp [εcap];positivity
  refine ⟨εcap,hεcap,(min_le_left _ _).trans he₀one,?_⟩
  intro ε hε he η γ hη hγ
  have he0:ε≤e₀:=he.trans (min_le_left _ _)
  have he1:ε≤1:=he0.trans he₀one
  have hefrac:ε≤1/(1+cLinear*cap₀):=he.trans (min_le_right _ _)
  let τ:=ordinarySafeCleanupScale r p (a*ε) (b*ε) (c*ε) (cap₀*ε^2)
  have hτcap:τ≤cap₀*ε^2:=by dsimp [τ,ordinarySafeCleanupScale];exact min_le_right _ _
  have hproduct:cLinear*cap₀*ε≤1:=by
    have hh:ε*(1+cLinear*cap₀)≤1:=(le_div_iff₀ (by positivity:0<1+cLinear*cap₀)).mp hefrac
    nlinarith only [hh,hε]
  have hτone:cLinear*τ≤1:=by
    have hh:=mul_le_mul_of_nonneg_left hτcap hLinear.le
    have heSq:ε^2≤ε:=by nlinarith [sq_nonneg ε]
    have hh':cLinear*(cap₀*ε^2)≤cLinear*cap₀*ε:=by
      nlinarith [mul_le_mul_of_nonneg_left heSq (show 0≤cLinear*cap₀ by positivity)]
    linarith only [hh,hh',hproduct]
  have hτmin:cLinear*τ≤min 1 η:=le_min hτone hη
  have hη':c'*τ≤(cGeom/K)*min 1 η:=by
    have hh:=mul_le_mul_of_nonneg_left hτmin (show 0≤cGeom/K by positivity)
    convert hh using 1 <;> dsimp [c'] <;> ring
  have hcubic:=hsmall ε hε he0 ((cGeom/K)*min 1 η) (by simpa only [τ] using hη')
  have hg:= (div_le_div_iff_of_pos_right hK).2 hγ
  have hg':(cGeom/K)*min 1 η≤γ/K:=by
    convert hg using 1 <;> ring
  have hh0:0≤(cGeom/K)*min 1 η:=by
    have hm0:0≤min (1:ℝ) η:=by
      apply le_min (by norm_num)
      have ht:0≤τ:=by
        have hlower:=ordinary_safe_cleanup_scale_quadratic_lower r p a b c cap₀ ε hp ha hb hc hcap hε.le he1
        exact (mul_nonneg hlower.1.le (sq_nonneg ε)).trans hlower.2
      nlinarith [mul_nonneg hLinear.le ht]
    positivity
  nlinarith only [hcubic,hg',hh0]
end Oberwolfach
