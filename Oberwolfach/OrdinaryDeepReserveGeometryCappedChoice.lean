module

public import Oberwolfach.OrdinaryDeepReserveGeometryParameterChoice

@[expose] public section
/-! Keep the explicit quadratic cleanup cap below one while selecting the
same root-geometry parameters. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_reserve_geometry_capped_choice
    (r m:ℕ) (p a b c cap₀ cLinear cGeom ξ ρ₀:ℝ)
    (hp:0<p) (ha:0<a) (hb:0<b) (hc:0<c) (hcap:0<cap₀)
    (hLinear:0<cLinear) (hGeom:0<cGeom) (hξ:0<ξ) (hρ:0<ρ₀):
    ∃εcap:ℝ,0<εcap ∧ εcap≤1 ∧ ∀ε:ℝ,0<ε→ε≤εcap→∀η γ:ℝ,
      cLinear*ordinarySafeCleanupScale r p (a*ε) (b*ε) (c*ε) (cap₀*ε^2)≤η→
      cGeom*min 1 η≤γ→
      cap₀*ε^2≤1 ∧ ∃lam:ℝ,0≤lam ∧ lam≤1/4 ∧ lam≤(ρ₀/8)/2 ∧
        lam≤γ/(1000*((m:ℝ)+2)) ∧ ε≤ξ/2 ∧ ε≤ξ*(ρ₀/8)/2 ∧ 2*ε^3≤lam :=by
  obtain ⟨e₀,he₀,he₀one,hmain⟩:=ordinary_deep_reserve_geometry_parameter_choice r m p a b c cap₀ cLinear cGeom ξ ρ₀
    hp ha hb hc hcap hLinear hGeom hξ hρ
  let εcap:ℝ:=min e₀ (1/(1+cap₀))
  have hεcap:0<εcap:=by dsimp [εcap];positivity
  refine ⟨εcap,hεcap,(min_le_left _ _).trans he₀one,?_⟩
  intro ε hε he η γ hη hγ
  have he0:ε≤e₀:=he.trans (min_le_left _ _)
  have he1:ε≤1:=he0.trans he₀one
  have hefrac:ε≤1/(1+cap₀):=he.trans (min_le_right _ _)
  have hlin:cap₀*ε≤1:=by
    have hh:ε*(1+cap₀)≤1:=(le_div_iff₀ (by positivity:0<1+cap₀)).mp hefrac
    nlinarith only [hh,hε]
  have hsq:ε^2≤ε:=by nlinarith [sq_nonneg ε]
  have hcap1:cap₀*ε^2≤1:=by
    have hh:=mul_le_mul_of_nonneg_left hsq hcap.le
    linarith only [hh,hlin]
  exact ⟨hcap1,hmain ε hε he0 η γ hη hγ⟩
end Oberwolfach
