module

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

theorem ordinary_assigned_marked_probability_upper
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hn:0<n) (hK:0<K) (m:ℕ) (hm:7≤m)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (i₀:Fin K) (rsv θ:ℝ) (hrs0:0≤rsv) (hrs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100)
    (hrsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,factorPreparationClass (F u) K=some i₀):
    ∀u g,ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) u g≤1/((m:ℝ)+1):=by
  have hm8:8≤(m:ℝ)+1:=by
    have hh:8≤m+1:=by omega
    exact_mod_cast hh
  have hreserve:=ordinary_class_reservation hn F hF Allowed hAllowed K hK i₀ rsv hrsclass hclass
  intro u g
  have hh:=ordinary_factor_actual_marginals hn (F u) (hF u) K hK i₀ rsv θ ((m:ℝ)+1)
    hrs0 hrs1 hθ.le hθ1 hm8 (hreserve u)
  have ha:ordinaryAssignedLongWeight F hF K θ ((m:ℝ)+1) u≤1/((m:ℝ)+1):=by
    simpa only [ordinaryAssignedLongWeight,ordinaryAssignedFraction] using hh.2.2.2.2.2.2.1
  cases g <;> simp only [ordinaryAssignedMarkedProbability,Bool.false_eq_true,ite_false,ite_true]
  · positivity
  · exact ha
end Oberwolfach
