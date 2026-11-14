module

public import Oberwolfach.OrdinaryAssignedReservoirRateInputs

@[expose] public section
/-! The correction theorem's lower rates can be selected from the original
abundance and index-density bounds before the factors and sample are known. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_correction_original_rate_choice
    (βfreq ρ₀:ℝ) (hβ:0<βfreq) (hβ1:βfreq ≤ 1) (hρ:0<ρ₀) (hρ1:ρ₀ ≤ 1):
    let smin:=βfreq/200
    let pstar:=ρ₀*smin/2
    let ω:=ρ₀/4;
    0<smin ∧ 0<pstar ∧ pstar ≤ 1 ∧ 0<ω ∧
    ∀{n D K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
      (F:U → SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
      (P:SimpleGraph (Fin n)) (hP:P.IsRegularOfDegree D) (hD:0<D)
      (i₀:Fin K) (rsv θ c:ℝ) (d:ℕ)
      (hρlo:ρ₀ ≤ initialIndexDensity U D) (hdegree:(1/2:ℝ)*(n:ℝ) ≤ D)
      (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d),
    let p:=initialIndexDensity U D*rsv/2;
    ω*n ≤ (Fintype.card U:ℝ) ∧ pstar ≤ p ∧ pstar ≤ 2*p ∧ pstar ≤ rsv ∧ rsv ≤ 1 ∧
    2*p=initialIndexDensity U D*rsv ∧
    (∀w,ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c w false=rsv) ∧
    (∀w,ordinaryAssignedMarkedProbability F hF K θ c w false=0) :=by
  intro smin pstar ω
  have hs:0<smin:=by dsimp [smin];positivity
  have hs1:smin ≤ 1:=by dsimp [smin];linarith
  have hp:0<pstar:=by dsimp [pstar];positivity
  have hp1:pstar ≤ 1:=by dsimp [pstar];nlinarith
  have hω:0<ω:=by dsimp [ω];positivity
  refine ⟨hs,hp,hp1,hω,?_⟩
  intro n D K U _ _ F hF P hP hD i₀ rsv θ c d hρlo hdegree sampling p
  have hpmin:2*pstar ≤ ρ₀*smin:=by dsimp [pstar];nlinarith
  obtain ⟨hU,hp0,hp2,hslo,hs1',hmean,hspoke,hmark⟩:=
    ordinary_assigned_reservoir_rate_inputs F hF P hP hD K i₀ rsv θ c ρ₀ smin pstar d
      hρ hρlo hdegree hp.le hpmin sampling
  refine ⟨?_,hp0,hp2,hslo,hs1',hmean,hspoke,hmark⟩
  dsimp [ω]
  nlinarith
end Oberwolfach
