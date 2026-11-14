module

public import Oberwolfach.MarkedCutThresholdBeforeRatio
public import Oberwolfach.MarkedFixedGeometryDeepRatioChoice

@[expose] public section
/-! A joint cut and two-step vortex parameter choice, with the cut threshold
chosen before the vortex ratio and the cut-set parameter chosen afterwards. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_vortex_cut_deep_hierarchy
    (r:ℕ) (α kstar tstar ζ hcap ρ ρ₀ t κ ξcap K εcap:ℝ)
    (hα:0<α) (hk:0<kstar) (htstar:0<tstar) (hζ:ζ≤tstar/16) (hhcap:0<hcap)
    (hρ:0<ρ) (hρ₀:0<ρ₀) (ht:0<t) (hκ:0<κ) (hξ:0<ξcap) (hK:0≤K) (hεcap:0<εcap):
    ∃ hcut ε₀:ℝ,0<hcut ∧ hcut≤hcap ∧ 2*hcut≤α*kstar/4 ∧ 2*hcut≤tstar/8-ζ ∧
      0<ε₀ ∧ ε₀≤εcap ∧ ε₀≤hcut ∧
      (∀ δcap:ℝ,0<δcap→∃ δ:ℝ,0<δ ∧ δ≤δcap ∧ δ<1/4 ∧ δ≤α/32 ∧ δ≤kstar/32 ∧ 2*δ≤tstar/8) ∧
      ∀ ε:ℝ,0<ε→ε≤ε₀→∃ ω ξ:ℝ,0<ω ∧ ω≤1 ∧ 0<ξ ∧
        ω≤ε/8 ∧ ω≤ρ₀*ε/64 ∧ ε^2≤ξ ∧ ξ≤ξcap ∧
        (4*K+(3*r+50:ℕ))*ξ≤κ/2 ∧ (1+2/ρ)*ξ≤t*ω/32:=by
  obtain ⟨hcut,hh,hhcap',hprod,hspoke,hδ⟩:=marked_cut_threshold_before_ratio α kstar tstar ζ hcap hα hk htstar hζ hhcap
  obtain ⟨ε₀,hε₀,hεcap,hchoose⟩:=marked_fixed_geometry_deep_ratio_choice r ρ ρ₀ t κ ξcap K (min εcap hcut)
    hρ hρ₀ ht hκ hξ hK (by positivity)
  refine ⟨hcut,ε₀,hh,hhcap',hprod,hspoke,hε₀,?_,?_,hδ,hchoose⟩
  · exact hεcap.trans (min_le_left _ _)
  · exact hεcap.trans (min_le_right _ _)
end Oberwolfach
