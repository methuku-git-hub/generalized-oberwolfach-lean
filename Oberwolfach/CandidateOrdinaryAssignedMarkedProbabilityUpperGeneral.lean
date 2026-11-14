module

public import Oberwolfach.OrdinaryAssignedMarkedProbabilityUpperGeneral
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.OrdinaryFactorActualMarginals
public import Oberwolfach.OrdinaryClassReservation
public import Oberwolfach.OrdinaryAssignedClassRecipe
public import Oberwolfach.RetainedRawIntervalRootUpperGeneral

@[expose] public section
/-! The sampled retained and raw interval roots at a hub have the needed
uniform upper bound for the actual assigned ordinary factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_marked_probability_upper_general_candidate
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hn:0<n) (hK:0<K) (c:ℝ) (hc:8≤c)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (i₀:Fin K) (rsv θ:ℝ) (hrs0:0≤rsv) (hrs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100)
    (hrsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,i₀∈factorShortCandidates (F u) K):
    ∀u g,ordinaryAssignedMarkedProbability F hF K θ c u g≤1/c:=by
  have hreserve:=ordinary_candidate_class_reservation hn F hF Allowed hAllowed K hK i₀ rsv hrsclass hclass
  intro u g
  have hh:=ordinary_factor_actual_marginals hn (F u) (hF u) K hK i₀ rsv θ c
    hrs0 hrs1 hθ.le hθ1 hc (hreserve u)
  have ha:ordinaryAssignedLongWeight F hF K θ c u≤1/c:=by
    simpa only [ordinaryAssignedLongWeight,ordinaryAssignedFraction] using hh.2.2.2.2.2.2.1
  cases g <;> simp only [ordinaryAssignedMarkedProbability,Bool.false_eq_true,ite_false,ite_true]
  · positivity
  · exact ha
end Oberwolfach
