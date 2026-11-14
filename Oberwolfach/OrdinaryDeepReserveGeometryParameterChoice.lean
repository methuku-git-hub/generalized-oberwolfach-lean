module

public import Oberwolfach.OrdinaryDeepReserveQuantitativeGeometry

@[expose] public section
/-! Choose the vortex scale before the later packing and geometry errors;
then the third-reserve size parameter satisfies all root-geometry caps. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_reserve_geometry_parameter_choice
    (r m:ℕ) (p a b c cap₀ cLinear cGeom ξ ρ₀:ℝ)
    (hp:0<p) (ha:0<a) (hb:0<b) (hc:0<c) (hcap:0<cap₀)
    (hLinear:0<cLinear) (hGeom:0<cGeom) (hξ:0<ξ) (hρ:0<ρ₀):
    ∃εcap:ℝ,0<εcap ∧ εcap≤1 ∧ ∀ε:ℝ,0<ε→ε≤εcap→∀η γ:ℝ,
      cLinear*ordinarySafeCleanupScale r p (a*ε) (b*ε) (c*ε) (cap₀*ε^2)≤η→
      cGeom*min 1 η≤γ→
      ∃lam:ℝ,0≤lam ∧ lam≤1/4 ∧ lam≤(ρ₀/8)/2 ∧
        lam≤γ/(1000*((m:ℝ)+2)) ∧ ε≤ξ/2 ∧ ε≤ξ*(ρ₀/8)/2 ∧ 2*ε^3≤lam :=by
  let K:ℝ:=1000*((m:ℝ)+2)
  have hK:0<K:=by dsimp [K];positivity
  obtain ⟨e₀,he₀,he₀one,hsmall⟩:=ordinary_deep_reserve_below_quantitative_geometry r p a b c cap₀ cLinear cGeom K
    hp ha hb hc hcap hLinear hGeom hK
  let εcap:ℝ:=min e₀ (min (1/8) (min (ρ₀/32) (min (ξ/2) (ξ*ρ₀/16))))
  have hεcap:0<εcap:=by dsimp [εcap];positivity
  refine ⟨εcap,hεcap,(min_le_left _ _).trans he₀one,?_⟩
  intro ε hε he η γ hη hγ
  have he0:ε≤e₀:=he.trans (min_le_left _ _)
  have heone:ε≤1:=he0.trans he₀one
  have he8:ε≤1/8:=he.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heρ:ε≤ρ₀/32:=he.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heξ:ε≤ξ/2:=he.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have heξρ:ε≤ξ*ρ₀/16:=he.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hcube:ε^3≤ε:=by
    have hsq:ε^2≤ε:=by nlinarith [sq_nonneg ε]
    have hh:=mul_le_mul_of_nonneg_left hsq hε.le
    nlinarith only [hh,hsq]
  have hgeom:=hsmall ε hε he0 η γ hη hγ
  refine ⟨2*ε^3,by positivity,?_,?_,?_,heξ,?_,le_rfl⟩
  · nlinarith only [hcube,he8]
  · nlinarith only [hcube,heρ]
  · simpa only [K] using hgeom
  · nlinarith only [heξρ]
end Oberwolfach
