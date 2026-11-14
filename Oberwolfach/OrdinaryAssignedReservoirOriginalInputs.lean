module

public import Oberwolfach.OrdinaryAssignedReferenceOriginalInputs

@[expose] public section

/-! Inputs for the corrected-reservoir theorem derived from the original
regular host and assigned sampling probabilities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_reservoir_original_inputs
    {n D:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (hP:P.IsRegularOfDegree D) (hD:0<D)
    (K:ℕ) (i₀:Fin K) (rsv θ c ρ₀ smin:ℝ) (d:ℕ)
    (hρ₀:0<ρ₀) (hρlo:ρ₀≤ initialIndexDensity U D)
    (hdegree:(1/2:ℝ)*(n:ℝ)≤D)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d):
    let p:=initialIndexDensity U D*rsv/2
    let q:=ordinaryAssignedMarkedProbability F hF K θ c
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c;
    0<Fintype.card U ∧ (ρ₀/4)*n≤(Fintype.card U:ℝ) ∧
    2*p=initialIndexDensity U D*rsv ∧
    (∀w,s w false=rsv) ∧ (∀w,q w false=0) ∧
    ρ₀*smin≤2*p ∧ ρ₀*smin≤rsv ∧ rsv≤1 :=by
  intro p q s
  obtain ⟨hU,hsize,_,hs,hq,hp,hr,hupper⟩:=
    ordinary_assigned_reference_original_inputs F hF P hP hD K i₀ rsv θ c ρ₀ smin d hρ₀ hρlo sampling
  have hD0:0≤(D:ℝ):=by positivity
  have hρD:ρ₀*(D:ℝ)≤ initialIndexDensity U D*(D:ℝ):=
    mul_le_mul_of_nonneg_right hρlo hD0
  have hρn:ρ₀*((1/2:ℝ)*(n:ℝ))≤ρ₀*(D:ℝ):=
    mul_le_mul_of_nonneg_left hdegree hρ₀.le
  refine ⟨hU,?_,?_,hs,hq,hp,hr,hupper⟩
  · nlinarith
  · dsimp [p]; ring
end Oberwolfach
