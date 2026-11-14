module

public import Oberwolfach.MarkedAdaptiveAuxiliaryConstants
public import Oberwolfach.LongAssignedHostMatchingWeights

@[expose] public section
/-! Choose the reference and level-density constants from the regular-host
margin, with exactly the dependencies needed by the adaptive event. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_host_adaptive_reference_parameters
    (m k₀:ℕ) (hm:1≤m) (αHost ρ₀:ℝ) (hα:0<αHost) (hρ₀:0<ρ₀)
    (hmargin:successorCycleRatio k₀+αHost/4≤1/2+αHost/2):
    ∃αRef γRich ω pstarRef kstar tstar:ℝ,
      αRef=αHost/2 ∧ 0<αRef ∧ 0<γRich ∧ γRich≤1/2 ∧ γRich≤αRef ∧
      successorCycleRatio k₀+αRef/2≤1/2+αRef ∧
      0<ω ∧ 0<pstarRef ∧ 0<kstar ∧ 0<tstar ∧ tstar≤1/100 ∧ tstar≤1 ∧
      4*ω≤ρ₀ ∧ 4*(m:ℝ)*pstarRef≤ρ₀*(1/100) ∧ tstar≤(1/100)/(m:ℝ) ∧
      (∀ρ:ℝ,ρ₀≤ρ→kstar≤ρ*(1/100)/2 ∧ kstar≤ρ*((1/100)/(m:ℝ))/2) := by
  obtain ⟨ω,pstarRef,kstar,tstar,hω,hp,hk,ht,ht100,ht1,hωBound,hpBound,htm,hkBound⟩:=
    marked_adaptive_auxiliary_constants m hm ρ₀ hρ₀
  let αRef:=αHost/2
  let γRich:=min (1/2:ℝ) αRef
  have hαRef:0<αRef:=by dsimp [αRef];positivity
  have hγ:0<γRich:=lt_min (by norm_num) hαRef
  have hγ1:γRich≤1/2:=min_le_left _ _
  have hγcap:γRich≤αRef:=min_le_right _ _
  have hmargin':successorCycleRatio k₀+αRef/2≤1/2+αRef:=by dsimp [αRef];linarith
  exact ⟨αRef,γRich,ω,pstarRef,kstar,tstar,rfl,hαRef,hγ,hγ1,hγcap,hmargin',
    hω,hp,hk,ht,ht100,ht1,hωBound,hpBound,htm,hkBound⟩
end Oberwolfach
