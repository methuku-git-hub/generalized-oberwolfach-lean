module

public import Oberwolfach.OrdinaryClassReserveBound
public import Oberwolfach.OrdinaryAssignedRetainedMass

@[expose] public section
/-! The actual class-frequency reserve alone gives the positive short weight
needed by the matching tests, without a cutoff-dependent reserve bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_short_weight_lower_direct_reserve
    {n:ℕ} (hn:0<n) {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ c:ℝ)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0≤θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hreserve:OrdinaryClassReserveBound F hF i₀ rsv):
    ∀u,(1/2:ℝ)≤ordinaryAssignedShortWeight F hF K i₀ rsv θ c u:=by
  intro u
  have hh:=ordinary_factor_actual_marginals hn (F u) (hF u) K hK i₀ rsv θ c hs0 hs1 hθ hθ1 hc (hreserve u)
  simpa only [ordinaryAssignedShortWeight,ordinaryAssignedLongWeight,ordinaryAssignedFraction] using hh.2.2.2.2.2.2.2.1
end Oberwolfach
