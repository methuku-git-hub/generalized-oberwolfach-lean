module

public import Oberwolfach.LongMatchingGeometryBetaChoice

@[expose] public section
/-! A single positive vortex parameter satisfies both the named matching
thresholds and the host geometry bounds. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_host_matching_beta_alignment
    (αHost αRef βmax εBal εRef κ x:ℝ)
    (hα:0<αRef) (hαeq:αRef=αHost/2) (hβ:0<βmax)
    (hBal:0<εBal) (hRef:0<εRef) (hκ:0<κ) (hx:0<x):
    ∃ βQ:ℝ,0<βQ ∧ βQ≤βmax ∧ βQ≤εBal/4 ∧ βQ≤εRef/4 ∧
      βQ≤1/4 ∧ βQ≤αRef/4 ∧ βQ≤αHost/8 ∧ βQ≤3*αHost/40 ∧
      βQ≤3/20 ∧ βQ≤κ ∧ βQ≤x := by
  obtain ⟨βQ,hβQ,hquarter,hαcap,hβcap,_,hbal,href,hκcap,hxcap,hgeom,hconst⟩:=
    long_matching_geometry_beta_choice αRef βmax βmax εBal εRef κ x hα hβ hβ hBal hRef hκ hx
  have hαhost:βQ≤αHost/8:=by rw [hαeq] at hαcap;linarith
  have hgeomhost:βQ≤3*αHost/40:=by rw [hαeq] at hgeom;linarith
  exact ⟨βQ,hβQ,hβcap,hbal,href,hquarter,hαcap,hαhost,hgeomhost,hconst,hκcap,hxcap⟩
end Oberwolfach
