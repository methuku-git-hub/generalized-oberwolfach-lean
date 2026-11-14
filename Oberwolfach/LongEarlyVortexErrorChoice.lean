module

public import Oberwolfach.LongResidualVortexClassCapChoice

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_early_vortex_error_choice
    (εAbs εRob γRich kstar tstar βList εMax:ℝ)
    (hAbs:0<εAbs) (hRob:0<εRob) (hγ:0<γRich) (hk:0<kstar)
    (ht:0<tstar) (hβ:0<βList) (hMax:0<εMax):
    ∃εQ:ℝ,0<εQ ∧ εQ<1/4 ∧ εQ≤εAbs ∧ εQ≤εRob ∧
      εQ≤min ((γRich/2)*kstar) tstar/128 ∧ εQ≤βList/32 ∧ εQ≤εMax := by
  let εQ:ℝ:=min (1/8) (min εAbs (min εRob
    (min (min ((γRich/2)*kstar) tstar/128) (min (βList/32) εMax))))
  have hε:0<εQ:=by dsimp [εQ]; positivity
  have h₁:εQ≤1/8:=min_le_left _ _
  have h₂:εQ≤min εAbs (min εRob (min (min ((γRich/2)*kstar) tstar/128) (min (βList/32) εMax))):=min_le_right _ _
  have hAbsCap:εQ≤εAbs:=h₂.trans (min_le_left _ _)
  have h₃:=h₂.trans (min_le_right _ _)
  have hRobCap:εQ≤εRob:=h₃.trans (min_le_left _ _)
  have h₄:=h₃.trans (min_le_right _ _)
  have hSmall:=h₄.trans (min_le_left _ _)
  have h₅:=h₄.trans (min_le_right _ _)
  exact ⟨εQ,hε,by linarith,hAbsCap,hRobCap,hSmall,h₅.trans (min_le_left _ _),h₅.trans (min_le_right _ _)⟩
end Oberwolfach
