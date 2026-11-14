module

public import Oberwolfach.OrdinaryVortexDeepTraceFineNumericExplicitLocalBalanceBeforeBeta

@[expose] public section
/-! The fine cover load and its balance tolerance can be chosen after an
arbitrary positive packing-balance margin, without using the cleanup rate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_sharp_fine_balance_rates_choice
    (ε δcut ρ₀ γ aCap:ℝ) (hε:0<ε) (hδ:0<δcut) (hρ:0<ρ₀) (hγ:0<γ) (haCap:0<aCap):
    ∃aLoad ξ η₀ ηbal ηInitial:ℝ,
      0<aLoad ∧ aLoad≤1 ∧ aLoad≤aCap ∧ aLoad≤γ/1000 ∧
      ξ=min (ε/200) (aLoad^2/160) ∧ 0<ξ ∧ ξ≤γ/160000 ∧
      η₀=δcut*(ρ₀/8)*ξ/1000 ∧ 0<η₀ ∧
      0<ηbal ∧ ηbal≤η₀ ∧ ηbal≤γ/1000 ∧ 0<ηInitial ∧ ηInitial≤ηbal ∧
      ηbal+100*ξ≤γ/8 ∧ ηInitial+100*ξ≤γ/8:=by
  let aLoad:ℝ:=min 1 (min (γ/1000) (aCap/2))
  have ha:0<aLoad:=by dsimp [aLoad];positivity
  have ha1:aLoad≤1:=min_le_left _ _
  have haγ:aLoad≤γ/1000:=(min_le_right _ _).trans (min_le_left _ _)
  have hacap:aLoad≤aCap:=by have hh: aLoad≤aCap/2:=(min_le_right _ _).trans (min_le_right _ _);linarith
  let ξ:ℝ:=min (ε/200) (aLoad^2/160)
  have hξ:0<ξ:=by dsimp [ξ];positivity
  have hξa:ξ≤aLoad^2/160:=min_le_right _ _
  have hasq:aLoad^2≤aLoad:=by nlinarith [mul_nonneg ha.le (sub_nonneg.mpr ha1)]
  have hξγ:ξ≤γ/160000:=by nlinarith only [hξa,hasq,haγ]
  let η₀:ℝ:=δcut*(ρ₀/8)*ξ/1000
  have hη₀:0<η₀:=by dsimp [η₀];positivity
  let ηbal:ℝ:=min (η₀/2) (γ/1000)
  have hη:0<ηbal:=by dsimp [ηbal];positivity
  have hηcap:ηbal≤η₀:=by have hh:=min_le_left (η₀/2) (γ/1000);dsimp [ηbal];linarith
  have hηγ:ηbal≤γ/1000:=min_le_right _ _
  refine ⟨aLoad,ξ,η₀,ηbal,ηbal/2,ha,ha1,hacap,haγ,rfl,hξ,hξγ,rfl,hη₀,hη,hηcap,hηγ,by positivity,by linarith,?_,?_⟩ <;> nlinarith only [hξγ,hηγ,hη.le,hγ.le]
end Oberwolfach
