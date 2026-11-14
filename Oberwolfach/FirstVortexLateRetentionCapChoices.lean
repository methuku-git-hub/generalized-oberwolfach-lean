module

public import Mathlib.Tactic

@[expose] public section
/-! Choose the retention tolerances after the active cap, vortex scale and
sampling rate, retaining an arbitrary earlier upper bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_late_retention_cap_choices
    (ε θ s active upper:ℝ) (hε:0<ε) (hθ:0<θ) (hs:0<s) (hactive:0<active) (hupper:0<upper):
    ∃ζRet ζret:ℝ,0<ζRet ∧ 0<ζret ∧ ζRet≤active/128 ∧
      ζret≤ζRet*ε/2 ∧ ζret≤s ∧ ζret≤θ/4096 ∧ ζret≤upper :=by
  let ζRet:ℝ:=active/256
  let ζret:ℝ:=min (ζRet*ε/4) (min (s/2) (min (θ/8192) (upper/2)))
  have hRet:0<ζRet:=by dsimp [ζRet];positivity
  have hret:0<ζret:=by dsimp [ζret];positivity
  have h1:ζret≤ζRet*ε/4:=min_le_left _ _
  have h2:ζret≤s/2:=(min_le_right _ _).trans (min_le_left _ _)
  have h3:ζret≤θ/8192:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4:ζret≤upper/2:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hp:0<ζRet*ε:=mul_pos hRet hε
  exact ⟨ζRet,ζret,hRet,hret,by dsimp [ζRet];linarith,by linarith,by linarith,by linarith,by linarith⟩
end Oberwolfach
