module

public import Oberwolfach.MarkedUniformCutParameterChoice

@[expose] public section
/-! Positive cut parameters in the notation of the cover-down record. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach

theorem marked_uniform_inner_cut_record_choice
    (α kstar tstar ζ δcap hcap:ℝ)
    (hα:0<α) (hk:0<kstar) (ht:0<tstar) (hζ:ζ≤tstar/16)
    (hδcap:0<δcap) (hhcap:0<hcap):
    ∃ δ hIcut:ℝ,0<δ ∧ δ≤δcap ∧ 0<hIcut ∧ hIcut≤hcap ∧
      δ≤α/32 ∧ δ≤kstar/32 ∧ 2*δ≤tstar/8 ∧
      2*hIcut≤α*kstar/4 ∧ 2*hIcut≤tstar/8-ζ:=by
  obtain ⟨δ,h,hδ,hδcap',hh,hhcap',hδα,hδk,hδt,hprod,hspoke⟩:=
    marked_uniform_inner_cut_parameter_choice α kstar tstar ζ δcap (2*hcap)
      hα hk ht hζ hδcap (by linarith)
  refine ⟨δ,h/2,hδ,hδcap',by linarith,?_,hδα,hδk,hδt,?_,?_⟩ <;> linarith
end Oberwolfach
