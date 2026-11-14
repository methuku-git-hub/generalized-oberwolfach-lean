module

public import Oberwolfach.OrdinaryDeepReserveFourteenthQuarticLoadScale

@[expose] public section
/-! A nine-step reserve fits the eighth-power geometry allowance when the
fresh sampling rate and boundary allowances are linear in the vortex scale. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_fifteen_step_quartic_geometry_scale
    (r m:ℕ) (p a b c cap₀ cLinear cGeom ξ ρ₀:ℝ)
    (hp:0<p) (ha:0<a) (hb:0<b) (hc:0<c) (hcap:0<cap₀)
    (hLinear:0<cLinear) (hGeom:0<cGeom) (hξ:0<ξ) (hρ:0<ρ₀):
    ∃εcap cLoad:ℝ,0<εcap ∧ εcap≤1 ∧ 0<cLoad ∧ cLoad≤1 ∧
    ∀ε:ℝ,0<ε→ε≤εcap→∀η γ:ℝ,
      cLinear*ordinarySafeCleanupScale r (p*ε^2) (a*ε) (b*ε) (c*ε^4) (cap₀*ε^14)≤η→
      cGeom*min 1 η≤γ→
      cap₀*ε^14≤1 ∧ ∃lam aLoad:ℝ,
        lam=2*ε^15 ∧ 0≤lam ∧ lam≤1/4 ∧ lam≤(ρ₀/8)/2 ∧
        lam≤γ/(1000*((m:ℝ)+2)) ∧ ε≤ξ/2 ∧ ε≤ξ*(ρ₀/8)/2 ∧ 2*ε^15≤lam ∧
        aLoad=cLoad*ε^14 ∧ 0<aLoad ∧ aLoad≤1 ∧ aLoad≤γ/(1000*((m:ℝ)+2)) :=by
  obtain ⟨cLoad,hLoad,hLoad1,hload⟩:=ordinary_deep_reserve_fourteenth_quartic_load_scale r m p a b c cap₀ cLinear cGeom
    hp ha hb hc hcap hLinear hGeom
  let εcap:ℝ:=min 1 (min (cLoad/2) (min (1/8) (min (ρ₀/32) (min (ξ/2) (min (ξ*ρ₀/16) (1/(1+cap₀)))))))
  have hεcap:0<εcap:=by dsimp [εcap];positivity
  refine ⟨εcap,cLoad,hεcap,min_le_left _ _,hLoad,hLoad1,?_⟩
  intro ε hε he η γ hη hγ
  have he1:ε≤1:=he.trans (min_le_left _ _)
  have heLoad:ε≤cLoad/2:=he.trans ((min_le_right _ _).trans (min_le_left _ _))
  have he8:ε≤1/8:=he.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heρ:ε≤ρ₀/32:=he.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have heξ:ε≤ξ/2:=he.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have heξρ:ε≤ξ*ρ₀/16:=he.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))
  have hefrac:ε≤1/(1+cap₀):=he.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))))
  have he8non:0≤ε^14:=pow_nonneg hε.le 14
  have he8one:ε^14≤1:=pow_le_one₀ hε.le he1
  have he9le:ε^15≤ε:=by
    have hh:=mul_le_mul_of_nonneg_right he8one hε.le
    nlinarith only [hh]
  have hcaplin:cap₀*ε≤1:=by
    have hh:ε*(1+cap₀)≤1:=(le_div_iff₀ (by positivity:0<1+cap₀)).mp hefrac
    nlinarith only [hh,hε]
  have he8le:ε^14≤ε:=by
    have h7:ε^13≤1:=pow_le_one₀ hε.le he1
    have hh:=mul_le_mul_of_nonneg_right h7 hε.le
    nlinarith only [hh]
  have hcap1:cap₀*ε^14≤1:=by
    have hh:=mul_le_mul_of_nonneg_left he8le hcap.le
    linarith only [hh,hcaplin]
  obtain ⟨ha0,ha1,haγ⟩:=hload ε hε he1 η γ hη hγ
  have hreserve:2*ε^15≤cLoad*ε^14:=by
    have hh:=mul_le_mul_of_nonneg_right heLoad he8non
    nlinarith only [hh]
  refine ⟨hcap1,2*ε^15,cLoad*ε^14,rfl,by positivity,?_,?_,hreserve.trans haγ,heξ,?_,le_rfl,rfl,ha0,ha1,haγ⟩
  · nlinarith only [he9le,he8]
  · nlinarith only [he9le,heρ]
  · nlinarith only [heξρ]
end Oberwolfach
