module

public import Oberwolfach.FirstVortexEventAuxiliaryChoices

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_reference_beta_geometry_cap
    (αRef βmax εBal εRef κ x:ℝ)
    (hα:0<αRef) (hβ:0<βmax) (hBal:0<εBal) (hRef:0<εRef) (hκ:0<κ) (hx:0<x):
    ∃βQ:ℝ,0<βQ ∧ βQ≤1/4 ∧ βQ≤αRef/4 ∧ βQ≤βmax ∧ βQ≤εBal/4 ∧ βQ≤εRef/4 ∧
      βQ≤(2*αRef)/8 ∧ βQ≤3*(2*αRef)/40 ∧ βQ≤3/20 ∧ βQ≤κ ∧ βQ≤x :=by
  let βcap:=min βmax (min (3*(2*αRef)/40) (min (3/20:ℝ) (min κ x)))
  have hcap:0<βcap:=by dsimp [βcap];positivity
  obtain ⟨βQ,hQ,hQ1,hQα,hQcap,hQBal,hQRef⟩:=first_vortex_reference_beta_choice αRef βcap εBal εRef hα hcap hBal hRef
  have hβmax:βQ≤βmax:=hQcap.trans (min_le_left _ _)
  have hrest:=hQcap.trans (min_le_right _ _)
  have hgeom:βQ≤3*(2*αRef)/40:=hrest.trans (min_le_left _ _)
  have hrest2:=hrest.trans (min_le_right _ _)
  have hsmall:βQ≤3/20:=hrest2.trans (min_le_left _ _)
  have hrest3:=hrest2.trans (min_le_right _ _)
  exact ⟨βQ,hQ,hQ1,hQα,hβmax,hQBal,hQRef,by linarith,hgeom,hsmall,hrest3.trans (min_le_left _ _),hrest3.trans (min_le_right _ _)⟩
end Oberwolfach
