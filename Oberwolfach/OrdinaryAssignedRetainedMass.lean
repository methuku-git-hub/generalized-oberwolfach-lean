module

public import Oberwolfach.OrdinaryAssignedKeptSupport
public import Oberwolfach.OrdinaryFactorActualMarginals
public import Oberwolfach.OrdinaryClassReservation

@[expose] public section
/-! The retained short frequencies and actual long sampling weight account for
all but the controlled unused fraction of each assigned factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_retained_mass
    {n:ℕ} (hn:0<n) {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (S:Set ℕ) (hS:∀u,AllowedCycleLengths (F u) S)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ c:ℝ)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,factorPreparationClass (F u) K=some i₀) (u:U):
    1-rsv-2*θ ≤ (1-θ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i)+
      c*ordinaryAssignedLongWeight F hF K θ c u :=by
  have hreserve:=ordinary_class_reservation hn F hF S hS K hK i₀ rsv hsclass hclass
  have hh:=ordinary_factor_actual_marginals hn (F u) (hF u) K hK i₀ rsv θ c hs0 hs1 hθ.le hθ1 hc (hreserve u)
  have hu:1-rsv-ordinaryAssignedLongWeight F hF K θ c u-
      ordinaryAssignedShortWeight F hF K i₀ rsv θ c u≤2*θ:=by
    simpa only [ordinaryAssignedShortWeight,ordinaryAssignedLongWeight,ordinaryAssignedFraction] using hh.2.2.2.2.1
  have hb:ordinaryAssignedShortWeight F hF K i₀ rsv θ c u=
      (c-1)*ordinaryAssignedLongWeight F hF K θ c u+
      (1-θ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i):=by
    rfl
  nlinarith [hu,hb]
end Oberwolfach
