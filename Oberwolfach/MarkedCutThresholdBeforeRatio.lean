module

public import Oberwolfach.MarkedUniformCutRecordChoice

@[expose] public section
/-! Choose the cut threshold before the vortex ratio; the separate cut-set
size parameter can still be made arbitrarily small afterwards. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_cut_threshold_before_ratio
    (α kstar tstar ζ hcap:ℝ)
    (hα:0<α) (hk:0<kstar) (ht:0<tstar) (hζ:ζ≤tstar/16) (hhcap:0<hcap):
    ∃ hcut:ℝ,0<hcut ∧ hcut≤hcap ∧ 2*hcut≤α*kstar/4 ∧ 2*hcut≤tstar/8-ζ ∧
      ∀ δcap:ℝ,0<δcap→∃ δ:ℝ,0<δ ∧ δ≤δcap ∧ δ<1/4 ∧
        δ≤α/32 ∧ δ≤kstar/32 ∧ 2*δ≤tstar/8:=by
  obtain ⟨δ₀,hcut,hδ₀,_,hh,hhcap',hδα,hδk,hδt,hprod,hspoke⟩:=
    marked_uniform_inner_cut_record_choice α kstar tstar ζ 1 hcap hα hk ht hζ (by norm_num) hhcap
  refine ⟨hcut,hh,hhcap',hprod,hspoke,?_⟩
  intro δcap hδcap
  let δ:=min δ₀ (min δcap (1/8))
  have hδ:0<δ:=by dsimp [δ];positivity
  have hδ₀':δ≤δ₀:=min_le_left _ _
  have hδcap':δ≤δcap:=(min_le_right _ _).trans (min_le_left _ _)
  have hδe:δ≤1/8:=(min_le_right _ _).trans (min_le_right _ _)
  exact ⟨δ,hδ,hδcap',by linarith,hδ₀'.trans hδα,hδ₀'.trans hδk,by linarith⟩
end Oberwolfach
