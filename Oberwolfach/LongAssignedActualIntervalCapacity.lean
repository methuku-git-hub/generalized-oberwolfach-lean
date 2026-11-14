module

public import Oberwolfach.LongAssignedComponentTotals
public import Oberwolfach.LongAssignedIntervalCapacity

@[expose] public section
/-! Use the original long-class hypothesis to discharge the component-size
and long-mass premises of the interval-capacity estimate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_assigned_actual_interval_capacity
    {n K:ℕ} {U A B:Type} [Fintype U] [DecidableEq U] [Fintype A] [Fintype B]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (S:Set ℕ) (hS:∀w,AllowedCycleLengths (F w) S) (hn:0<n) (hK:0<K)
    (hclass:∀w,factorPreparationClass (F w) K=none)
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (hd:0<d) (θ:ℝ) (hθ:0<θ)
    (raw:RawIntervalFamilyOutcome (Fin n) U Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d raw false) t) (w:U)
    (index:A⊕B ≃ retainedAndRawIntervalIndex π d raw false true t J w)
    (hcut:5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K+1)≤θ/2)
    (hlarge:8*((m:ℝ)+1)/θ<(n:ℝ)^((1:ℝ)/4))
    (hcounts:∀g,|rawIntervalHubStartCount π d g raw w-
      (n:ℝ)*longAssignedIntervalProbability F hF K m θ w g/d|<(n:ℝ)^(3/4:ℝ)/d):
    let I:={C:(F w).ConnectedComponent // K<Fintype.card C}
    let components:I↪(F w).ConnectedComponent:=Function.Embedding.subtype _
    Fintype.card (A⊕B)≤∑i:I,Fintype.card (components i)/((m+1)*d+5):=by
  intro I components
  have ⟨hlong,hell,htotal⟩:=long_assigned_component_totals hn F hF S hS hK hclass w
  apply long_assigned_interval_capacity_from_start_counts F hF π d m (K+1) hd hn (by omega) θ hθ raw t J w index components hlong hell htotal
  · simpa only [Nat.cast_add,Nat.cast_one] using hcut
  · exact hlarge
  · exact hcounts
end Oberwolfach
