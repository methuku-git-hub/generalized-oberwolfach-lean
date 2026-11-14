module

public import Oberwolfach.OrdinaryAssignedVortexExactSamplingData
public import Oberwolfach.OrdinaryReferenceCentreFromRegularHost

@[expose] public section
/-! Reference means and nonempty hub type follow from the original regular
host and the positive lower bound for the assigned sampling density. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_reference_original_inputs
    {n D:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (hP:P.IsRegularOfDegree D) (hD:0<D)
    (K:ℕ) (i₀:Fin K) (rsv θ c ρ₀ smin:ℝ) (d:ℕ)
    (hρ₀:0<ρ₀) (hρlo:ρ₀≤ initialIndexDensity U D)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d):
    0<Fintype.card U ∧
    initialIndexDensity U D*(D:ℝ)=2*(Fintype.card U:ℝ) ∧
    (∀v,(2*(initialIndexDensity U D*rsv/2))*(P.degree v:ℝ)=2*(rsv*Fintype.card U)) ∧
    (∀w,ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c w false=rsv) ∧
    (∀w,ordinaryAssignedMarkedProbability F hF K θ c w false=0) ∧
    ρ₀*smin≤2*(initialIndexDensity U D*rsv/2) ∧ ρ₀*smin≤rsv ∧ rsv≤1 :=by
  have hDreal:0<(D:ℝ):=by exact_mod_cast hD
  have hρ:0< initialIndexDensity U D:=hρ₀.trans_le hρlo
  have hsize:initialIndexDensity U D*(D:ℝ)=2*(Fintype.card U:ℝ):=by
    simp [initialIndexDensity,ne_of_gt hDreal]
  have hU:0<Fintype.card U:=by
    have hpos:0<(Fintype.card U:ℝ):=by nlinarith [mul_pos hρ hDreal]
    exact_mod_cast hpos
  have hp:2*(initialIndexDensity U D*rsv/2)=initialIndexDensity U D*rsv:=by ring
  refine ⟨hU,hsize,ordinary_reference_centre_from_regular_host P D hP (initialIndexDensity U D) rsv _ hsize hp,
    sampling.hfalse,?_,sampling.hpmin,sampling.hsmin,sampling.hrsv⟩
  intro w
  simp [ordinaryAssignedMarkedProbability]
end Oberwolfach
