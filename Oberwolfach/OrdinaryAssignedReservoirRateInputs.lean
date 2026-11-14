module

public import Oberwolfach.OrdinaryAssignedReservoirOriginalInputs

@[expose] public section
/-! One lower rate serves both the correction theorem, which uses twice the
rim probability, and the reserved target lists, which use the rim probability. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_reservoir_rate_inputs
    {n D:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (hP:P.IsRegularOfDegree D) (hD:0<D)
    (K:ℕ) (i₀:Fin K) (rsv θ c ρ₀ smin pstar:ℝ) (d:ℕ)
    (hρ₀:0<ρ₀) (hρlo:ρ₀≤ initialIndexDensity U D)
    (hdegree:(1/2:ℝ)*(n:ℝ)≤D) (hpstar:0≤pstar) (hpmin:2*pstar≤ρ₀*smin)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d):
    let p:=initialIndexDensity U D*rsv/2;
    ρ₀*n≤4*(Fintype.card U:ℝ) ∧ pstar≤p ∧ pstar≤2*p ∧ pstar≤ rsv ∧ rsv≤1 ∧
    2*p=initialIndexDensity U D*rsv ∧
    (∀w,ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c w false=rsv) ∧
    (∀w,ordinaryAssignedMarkedProbability F hF K θ c w false=0) :=by
  intro p
  obtain ⟨_,hU,hmean,hs,hzero,hp,hrsv,hrsv1⟩:=
    ordinary_assigned_reservoir_original_inputs F hF P hP hD K i₀ rsv θ c ρ₀ smin d hρ₀ hρlo hdegree sampling
  refine ⟨?_,?_,?_,?_,hrsv1,hmean,hs,hzero⟩ <;> (try dsimp only [p]) <;> nlinarith
end Oberwolfach
