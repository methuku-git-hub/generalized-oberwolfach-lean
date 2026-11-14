module

public import Oberwolfach.OrdinaryAssignedWheelSampleInputs

@[expose] public section
/-! The actual assigned law supplies the rim and hub rates required by the
inner-hub and endpoint event selectors. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_inner_endpoint_law_inputs
    {n D:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (hP:P.IsRegularOfDegree D) (hD:0<D)
    (K:ℕ) (i₀:Fin K) (rsv θ c ρ₀ smin pmin:ℝ) (d:ℕ)
    (hρ₀:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hsmin:0<smin) (hstar:pmin≤ρ₀*smin/2)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d):
    let p:=initialIndexDensity U D*rsv/2;
    pmin≤2*p ∧ 2*p≤1 ∧ pmin≤rsv ∧ 0<rsv ∧ rsv≤1 ∧
    2*p=initialIndexDensity U D*rsv ∧
    (∀u,ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c u false=rsv) :=by
  intro p
  obtain ⟨_,hpR,hpR1,hpH,hrsv,hrsv1,heq,hsp⟩:=
    ordinary_assigned_wheel_sample_inputs F hF P hP hD K i₀ rsv θ c ρ₀ smin d hρ₀ hρlo hρhi hsmin sampling
  exact ⟨hstar.trans hpR,hpR1,hstar.trans hpH,hrsv,hrsv1,heq,hsp⟩
end Oberwolfach
