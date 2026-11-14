module

public import Oberwolfach.OrdinaryAssignedRetainedMass
public import Oberwolfach.OrdinaryAbundanceReservation

@[expose] public section
/-! The manuscript's assigned short-wheel weight has a uniform positive
lower bound, so matching extraction can take its threshold before the graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_short_weight_uniform_lower
    {n:ℕ} (hn:0<n) {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (S:Set ℕ) (hS:∀u,AllowedCycleLengths (F u) S)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ c:ℝ)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0≤θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,factorPreparationClass (F u) K=some i₀):
    ∀u,(1/2:ℝ)≤ordinaryAssignedShortWeight F hF K i₀ rsv θ c u:=by
  have hreserve:=ordinary_class_reservation hn F hF S hS K hK i₀ rsv hsclass hclass
  intro u
  have hh:=ordinary_factor_actual_marginals hn (F u) (hF u) K hK i₀ rsv θ c hs0 hs1 hθ hθ1 hc (hreserve u)
  simpa only [ordinaryAssignedShortWeight,ordinaryAssignedLongWeight,ordinaryAssignedFraction] using hh.2.2.2.2.2.2.2.1

theorem ordinary_assigned_short_weight_lower_from_abundance
    {n:ℕ} (hn:0<n) {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (β rsv θ c:ℝ)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0≤θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hrsv:rsv≤β)
    (hfreq:∀u,β*n≤((Finset.univ.filter (fun v=>Fintype.card ((F u).connectedComponentMk v)=i₀.val+1)).card:ℝ)):
    ∀u,(1/2:ℝ)≤ordinaryAssignedShortWeight F hF K i₀ rsv θ c u:=by
  have hreserve:=ordinary_reservation_from_specified_abundance hn F hF K i₀ β rsv hrsv hfreq
  intro u
  have hh:=ordinary_factor_actual_marginals hn (F u) (hF u) K hK i₀ rsv θ c hs0 hs1 hθ hθ1 hc (hreserve u)
  simpa only [ordinaryAssignedShortWeight,ordinaryAssignedLongWeight,ordinaryAssignedFraction] using hh.2.2.2.2.2.2.2.1
end Oberwolfach
