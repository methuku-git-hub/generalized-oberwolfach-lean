module

public import Oberwolfach.MarkedDeepGapUniformTransfer

@[expose] public section
/-! The vortex ratio and deep-error choice depend only on fixed lower density
bounds, and so remain valid for the actual densities chosen later. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_uniform_vortex_cut_deep_hierarchy
    (r:ℕ) (α kstar tstar ζ hcap ρ₀ κ ξcap K εcap:ℝ)
    (hα:0<α) (hk:0<kstar) (htstar:0<tstar) (hζ:ζ≤tstar/16) (hhcap:0<hcap)
    (hρ₀:0<ρ₀) (hκ:0<κ) (hξ:0<ξcap) (hK:0≤K) (hεcap:0<εcap):
    ∃ hcut ε₀:ℝ,0<hcut ∧ hcut≤hcap ∧ 2*hcut≤α*kstar/4 ∧ 2*hcut≤tstar/8-ζ ∧
      0<ε₀ ∧ ε₀≤εcap ∧ ε₀≤hcut ∧
      (∀ δcap:ℝ,0<δcap→∃ δ:ℝ,0<δ ∧ δ≤δcap ∧ δ<1/4 ∧ δ≤α/32 ∧ δ≤kstar/32 ∧ 2*δ≤tstar/8) ∧
      ∀ ε:ℝ,0<ε→ε≤ε₀→∃ ω ξ:ℝ,0<ω ∧ ω≤1 ∧ 0<ξ ∧
        ω≤ε/8 ∧ ω≤ρ₀*ε/64 ∧ ε^2≤ξ ∧ ξ≤ξcap ∧
        (4*K+(3*r+50:ℕ))*ξ≤κ/2 ∧
        ∀ ρ t:ℝ,ρ₀≤ρ→tstar≤t→(1+2/ρ)*ξ≤t*ω/32:=by
  obtain ⟨hcut,ε₀,hh,hhcap',hp,hs,he,hecap,heh,hdelta,hchoose⟩:=
    marked_vortex_cut_deep_hierarchy r α kstar tstar ζ hcap ρ₀ ρ₀ tstar κ ξcap K εcap
      hα hk htstar hζ hhcap hρ₀ hρ₀ htstar hκ hξ hK hεcap
  refine ⟨hcut,ε₀,hh,hhcap',hp,hs,he,hecap,heh,hdelta,?_⟩
  intro ε hε hεbound
  obtain ⟨ω,ξ,hw,hw1,hxi,hwε,hwρ,hεxi,hxicap,hxigeom,hgap⟩:=hchoose ε hε hεbound
  refine ⟨ω,ξ,hw,hw1,hxi,hwε,hwρ,hεxi,hxicap,hxigeom,?_⟩
  intro ρ t hρ ht
  exact marked_deep_gap_uniform_transfer ρ₀ ρ tstar t ω ξ hρ₀ hρ ht (le_of_lt hw) (le_of_lt hxi) hgap
end Oberwolfach
