module

public import Oberwolfach.OrdinaryDeepFifteenStepQuarticGeometryScale
public import Oberwolfach.OrdinaryExplicitCorrectionTwentyEighthScale

@[expose] public section
/-! Compatible geometry and explicit correction rates for a fifteen-step reserve. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_fifteen_quartic_geometry_cover_scale_choice
    (r m:ℕ) (p a b c cap₀ cLinear cGeom ξ ρ₀ δcut:ℝ)
    (hp:0<p) (ha:0<a) (hb:0<b) (hc:0<c) (hcap:0<cap₀)
    (hLinear:0<cLinear) (hGeom:0<cGeom) (hξ:0<ξ) (hρ:0<ρ₀) (hδ:0<δcut):
    ∃εcap cLoad cEta:ℝ,0<εcap ∧ εcap≤1 ∧ 0<cLoad ∧ cLoad≤1 ∧ 0<cEta ∧
    ∀ε:ℝ,0<ε→ε≤εcap→∀η γ:ℝ,
      cLinear*ordinarySafeCleanupScale r (p*ε^2) (a*ε) (b*ε) (c*ε^4) (cap₀*ε^14)≤η→
      cGeom*min 1 η≤γ→
    ∃lam aLoad ξroot ηcover:ℝ,
      cap₀*ε^14≤1 ∧ 0≤lam ∧ lam≤1/4 ∧ lam≤(ρ₀/8)/2 ∧ lam≤γ/(1000*((m:ℝ)+2)) ∧
      ε≤ξ/2 ∧ ε≤ξ*(ρ₀/8)/2 ∧ 2*ε^15≤lam ∧
      aLoad=cLoad*ε^14 ∧ 0<aLoad ∧ aLoad≤1 ∧ aLoad≤γ/(1000*((m:ℝ)+2)) ∧
      ξroot=min (ε/200) (aLoad^2/160) ∧ 0<ξroot ∧
      ηcover=δcut*(ρ₀/8)*ξroot/1000 ∧ cEta*ε^28≤ηcover :=by
  obtain ⟨εcap,cLoad,hεcap,hεcap1,hLoad,hLoad1,hgeometry⟩:=
    ordinary_deep_fifteen_step_quartic_geometry_scale r m p a b c cap₀ cLinear cGeom ξ ρ₀
      hp ha hb hc hcap hLinear hGeom hξ hρ
  obtain ⟨cEta,hEta,hcorrect⟩:=ordinary_explicit_correction_twenty_eighth_lower δcut ρ₀ cLoad hδ hρ hLoad
  refine ⟨εcap,cLoad,cEta,hεcap,hεcap1,hLoad,hLoad1,hEta,?_⟩
  intro ε hε he η γ hη hγ
  have he1:ε≤1:=he.trans hεcap1
  obtain ⟨hcap1,lam,aLoad,hlamEq,hlam,hlam1,hlamρ,hlamγ,hεξ,hερ,hεroot,haEq,ha0,ha1,haγ⟩:=
    hgeometry ε hε he η γ hη hγ
  let ξroot:ℝ:=min (ε/200) (aLoad^2/160)
  let ηcover:ℝ:=δcut*(ρ₀/8)*ξroot/1000
  have hξroot:0<ξroot:=by dsimp [ξroot];positivity
  have hlower:cEta*ε^28≤ηcover:=by
    simpa only [ηcover,ξroot,haEq] using hcorrect ε hε he1
  exact ⟨lam,aLoad,ξroot,ηcover,hcap1,hlam,hlam1,hlamρ,hlamγ,hεξ,hερ,hεroot,haEq,ha0,ha1,haγ,rfl,hξroot,rfl,hlower⟩
end Oberwolfach
