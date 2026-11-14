module

public import Oberwolfach.OrdinaryDeepReserveGeometryCappedChoice
public import Oberwolfach.OrdinaryDeepReserveLoadScale
public import Oberwolfach.OrdinaryExplicitCorrectionScale

@[expose] public section
/-! Select the vortex, cleanup, root and cover scales in their dependency order. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_geometry_cover_scale_choice
    (r m:ℕ) (p a b c cap₀ cLinear cGeom ξ ρ₀ δcut:ℝ)
    (hp:0<p) (ha:0<a) (hb:0<b) (hc:0<c) (hcap:0<cap₀)
    (hLinear:0<cLinear) (hGeom:0<cGeom) (hξ:0<ξ) (hρ:0<ρ₀) (hδ:0<δcut):
    ∃εcap cLoad cEta:ℝ,0<εcap ∧ εcap≤1 ∧ 0<cLoad ∧ cLoad≤1 ∧ 0<cEta ∧
    ∀ε:ℝ,0<ε→ε≤εcap→∀η γ:ℝ,
      cLinear*ordinarySafeCleanupScale r p (a*ε) (b*ε) (c*ε) (cap₀*ε^2)≤η→
      cGeom*min 1 η≤γ→
    ∃lam aLoad ξroot ηcover:ℝ,
      cap₀*ε^2≤1 ∧ 0≤lam ∧ lam≤1/4 ∧ lam≤(ρ₀/8)/2 ∧ lam≤γ/(1000*((m:ℝ)+2)) ∧
      ε≤ξ/2 ∧ ε≤ξ*(ρ₀/8)/2 ∧ 2*ε^3≤lam ∧
      aLoad=cLoad*ε^2 ∧ 0<aLoad ∧ aLoad≤1 ∧ aLoad≤γ/(1000*((m:ℝ)+2)) ∧
      ξroot=min (ε/200) (aLoad^2/160) ∧ 0<ξroot ∧
      ηcover=δcut*(ρ₀/8)*ξroot/1000 ∧ cEta*ε^4≤ηcover :=by
  obtain ⟨εcap,hεcap,hεcap1,hgeometry⟩:=ordinary_deep_reserve_geometry_capped_choice r m p a b c cap₀ cLinear cGeom ξ ρ₀
    hp ha hb hc hcap hLinear hGeom hξ hρ
  obtain ⟨cLoad,hcLoad,hcLoad1,hload⟩:=ordinary_deep_reserve_quadratic_load_scale r m p a b c cap₀ cLinear cGeom
    hp ha hb hc hcap hLinear hGeom
  obtain ⟨cEta,hcEta,hcorrect⟩:=ordinary_explicit_correction_quartic_lower δcut ρ₀ cLoad hδ hρ hcLoad
  refine ⟨εcap,cLoad,cEta,hεcap,hεcap1,hcLoad,hcLoad1,hcEta,?_⟩
  intro ε hε he η γ hη hγ
  have he1:ε≤1:=he.trans hεcap1
  obtain ⟨hcap1,lam,hlam,hlam1,hlamρ,hlamγ,hεξ,hερ,hεroot⟩:=hgeometry ε hε he η γ hη hγ
  obtain ⟨hload0,hload1,hloadγ⟩:=hload ε hε he1 η γ hη hγ
  let aLoad:ℝ:=cLoad*ε^2
  let ξroot:ℝ:=min (ε/200) (aLoad^2/160)
  let ηcover:ℝ:=δcut*(ρ₀/8)*ξroot/1000
  have hξroot:0<ξroot:=by dsimp [ξroot,aLoad];positivity
  have hlower:cEta*ε^4≤ηcover:=by
    simpa only [ηcover,ξroot,aLoad] using hcorrect ε hε he1
  exact ⟨lam,aLoad,ξroot,ηcover,hcap1,hlam,hlam1,hlamρ,hlamγ,hεξ,hερ,hεroot,rfl,hload0,hload1,hloadγ,rfl,hξroot,rfl,hlower⟩
end Oberwolfach
