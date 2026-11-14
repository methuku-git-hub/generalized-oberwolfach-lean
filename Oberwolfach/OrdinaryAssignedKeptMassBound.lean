module

public import Oberwolfach.OrdinaryAssignedRetainedMass
public import Oberwolfach.OrdinaryFactorFrequencyPartition

@[expose] public section
/-! The total retained short-cycle frequency never exceeds the unreserved
factor fraction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_kept_mass_le_unreserved
    {n:ℕ} (hn:0<n) {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ:ℝ) (hrs:0≤rsv)
    (hrsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,factorPreparationClass (F u) K=some i₀) (u:U):
    (∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i)≤1-rsv:=by
  have hreserve:=ordinary_class_reservation hn F hF Allowed hAllowed K hK i₀ rsv hrsclass hclass
  have hp:=ordinary_factor_frequency_partition hn (F u) (hF u) K hK i₀ rsv hrs (hreserve u)
  let f:=fun i:Fin K=>ordinaryAssignedFraction F hF K u (some i)-(if i=i₀ then rsv else 0)
  have hf:∀i,0≤f i:=by
    simpa only [f,ordinaryAssignedFraction] using hp.1
  have hlong:0≤ordinaryAssignedFraction F hF K u none:=by
    simpa only [ordinaryAssignedFraction] using hp.2.1
  have hpart:(∑i:Fin K,f i)+ordinaryAssignedFraction F hF K u none=1-rsv:=by
    simpa only [f,ordinaryAssignedFraction] using hp.2.2
  have hsum:(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i)≤∑i:Fin K,f i:=by
    apply Finset.sum_le_sum
    intro i _
    change (if f i<θ/(100*(K:ℝ)) then 0 else f i)≤f i
    split
    · exact hf i
    · exact le_rfl
  linarith
end Oberwolfach
