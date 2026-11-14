module

public import Oberwolfach.CandidateOrdinaryAssignedSamplingParametersDirectReserve
public import Oberwolfach.OrdinaryAssignedVortexExactSamplingData

@[expose] public section

/-! Under the original direct-reserve recipe, every hub's unassigned
interval-state mass is at most twice the matching slack. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_exact_assigned_hub_slack_upper
    {n D:ℕ} (hn:0<n) (hD:0<D) {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ c:ℝ) (d:ℕ) (hd:2≤d)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hda:1/θ≤d) (hρ:0 < initialIndexDensity U D) (hρ1:initialIndexDensity U D≤1)
    (S:Set ℕ) (hS:∀w,AllowedCycleLengths (F w) S)
    (hClass:OrdinaryClassReserveBound F hF i₀ rsv):
    ∀w,1-(∑g,ordinaryAssignedMarkedProbability F hF K θ c w g)-
      (∑j,ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c w j)≤2*θ :=by
  let ρ:=initialIndexDensity U D
  have hDr:0<(D:ℝ):=by exact_mod_cast hD
  have hsize:ρ*(D:ℝ)=2*(Fintype.card U:ℝ):=by
    simp [ρ,initialIndexDensity,ne_of_gt hDr]
  have hh:=ordinary_class_assigned_sampling_parameters_candidate_direct_reserve hn F hF K hK i₀ rsv θ c ρ D d hd
    hs0 hs1 hθ hθ1 hc hda hρ hρ1 hDr hsize S hS hClass
  intro w
  have hw:1-rsv-ordinaryAssignedLongWeight F hF K θ c w-
      ordinaryAssignedShortWeight F hF K i₀ rsv θ c w≤2*θ:=by
    simpa only [ordinaryAssignedShortWeight,ordinaryAssignedLongWeight,ordinaryAssignedFraction] using
      (hh.1 w).2.2.2.2.1
  dsimp only [ordinaryAssignedMarkedProbability,ordinaryAssignedSpokeProbability]
  simp only [Fintype.sum_bool,Bool.false_eq_true,ite_false,ite_true]
  linarith
end Oberwolfach
