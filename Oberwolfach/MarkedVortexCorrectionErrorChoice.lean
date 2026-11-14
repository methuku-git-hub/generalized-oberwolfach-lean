module

public import Mathlib.Tactic

@[expose] public section
/-! The vortex error can meet the matching, correction, and geometric
caps simultaneously before the host is chosen. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_vortex_correction_error_choice
    (εAbs εRob εGeom γRich kstar tstar:ℝ)
    (hAbs:0<εAbs) (hRob:0<εRob) (hGeom:0<εGeom) (hγ:0<γRich) (hk:0<kstar) (ht:0<tstar):
    ∃ εQ:ℝ,0<εQ ∧ εQ<1/4 ∧ εQ≤εAbs ∧ εQ≤εRob ∧ εQ≤εGeom ∧
      εQ≤min ((γRich/2)*kstar) tstar/128:=by
  let cut:=min ((γRich/2)*kstar) tstar/128
  let cap:=min (1/4:ℝ) (min εAbs (min εRob (min εGeom cut)))
  have hcut:0<cut:=by dsimp [cut];positivity
  have hcap:0<cap:=by dsimp [cap];positivity
  have hquarter:cap≤1/4:=by dsimp [cap];exact min_le_left _ _
  have hAbsCap:cap≤εAbs:=by dsimp [cap];exact (min_le_right _ _).trans (min_le_left _ _)
  have hRobCap:cap≤εRob:=by dsimp [cap];exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hGeomCap:cap≤εGeom:=by dsimp [cap];exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hcutCap:cap≤cut:=by dsimp [cap];exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨cap/2,by positivity,by linarith,by linarith,by linarith,by linarith,?_⟩
  dsimp [cut] at hcutCap
  linarith
end Oberwolfach
