module

public import Oberwolfach.OrdinaryDeepCommonSampleFailureBudget

@[expose] public section
/-! Choose the long structural common-event errors after the original failure
allowance, while keeping its single high-probability event. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_original_high_probability_failure_budget (χ:ℝ) (hχ:0<χ) (hχone:χ<1):
    ∃ε₀ ηEvent:ℝ,0<ε₀ ∧ ε₀<1 ∧ 0<ηEvent ∧
      0<1-(36*(ε₀+6*ηEvent)+ηEvent) ∧
      36*(ε₀+6*ηEvent)+ηEvent≤χ ∧
      (∀n:ℕ,∀p:ℝ,1-(36*(ε₀+6*ηEvent)+ηEvent)≤p→1-χ-1/(n:ℝ)^10≤p) ∧
      (∀εExtra:ℝ,0<εExtra→4*εExtra≤ε₀→
        ∃t:ℝ,0<t ∧ t+t+t+2*t+t+t+t+εExtra<ε₀) :=by
  let ε₀:ℝ:=χ/100
  let ηEvent:ℝ:=χ/10000
  have hε₀:0<ε₀:=by dsimp [ε₀];positivity
  have hη:0<ηEvent:=by dsimp [ηEvent];positivity
  have hε₀one:ε₀<1:=by dsimp [ε₀];linarith
  have hbound:36*(ε₀+6*ηEvent)+ηEvent≤χ:=by dsimp [ε₀,ηEvent];linarith
  refine ⟨ε₀,ηEvent,hε₀,hε₀one,hη,by linarith,hbound,?_,?_⟩
  · intro n p hp
    have hnonneg:0≤1/(n:ℝ)^10:=by positivity
    linarith
  · intro εExtra hExtra hExtraCap
    refine ⟨ε₀/32,by positivity,?_⟩
    linarith
end Oberwolfach
