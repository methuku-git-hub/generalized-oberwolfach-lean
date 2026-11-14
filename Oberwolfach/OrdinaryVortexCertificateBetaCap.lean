module

public import Oberwolfach.OrdinaryDeepParentAfterFailureAllCaps

@[expose] public section
/-! A single late vortex-error cap simultaneously respects all four
certificate thresholds. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_vortex_certificate_beta_cap
    (βcap δInitial δDeep δedit:ℝ) (hβ:0<βcap) (hI:0<δInitial) (hD:0<δDeep) (hE:0<δedit):
    ∃cap:ℝ,0<cap ∧ cap≤βcap ∧ cap≤δInitial ∧ cap≤δDeep ∧ cap≤δedit :=by
  let cap:=min βcap (min δInitial (min δDeep δedit))
  exact ⟨cap,by dsimp [cap];positivity,min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩
end Oberwolfach
