module

public import Oberwolfach.FirstVortexEarlyAlphaVortexCap

@[expose] public section
/-! Choose the matching robustness and its admissible vortex cap from the
original positive host and list scales, before the sampling rates. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_early_matching_base
    (ρ₀ δglobal lamList βfinal εcap:ℝ)
    (hρ:0<ρ₀) (hδ:0<δglobal) (hlist:0<lamList)
    (hβ:0≤βfinal) (hβbound:βfinal≤lamList/4) (hcap:0<εcap):
    ∃bmatch α εupper:ℝ,0<bmatch ∧ bmatch≤((ρ₀/4)/40000)/16 ∧
      0<α ∧ (2*α)/16≤bmatch ∧ 2*α≤4*δglobal ∧
      0<εupper ∧ εupper≤εcap ∧ εupper≤δglobal ∧ βfinal+εupper≤lamList ∧
      ∀ε:ℝ,ε≤εupper→ε≤α/1000 ∧ ε≤(ρ₀/4)/80000 ∧ ε≤((ρ₀/4)/40000)/8192 :=by
  let bmatch:ℝ:=((ρ₀/4)/40000)/32
  have hb:0<bmatch:=by dsimp [bmatch];positivity
  obtain ⟨α,εupper,hα,hαb,hαδ,hε,hεcap,hεδ,hεlist,hεα,hερ,hεprecise⟩:=
    first_vortex_early_alpha_vortex_cap bmatch ρ₀ δglobal lamList βfinal εcap hb hρ hδ hlist hβ hβbound hcap
  refine ⟨bmatch,α,εupper,hb,?_,hα,hαb,hαδ,hε,hεcap,hεδ,hεlist,?_⟩
  · dsimp [bmatch];linarith
  · intro ε hεupper
    exact ⟨hεupper.trans hεα,hεupper.trans hερ,hεupper.trans hεprecise⟩
end Oberwolfach
