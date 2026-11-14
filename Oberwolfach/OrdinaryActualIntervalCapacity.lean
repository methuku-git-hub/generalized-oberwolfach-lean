module

public import Oberwolfach.OrdinaryAssignedIntervalCapacity
public import Oberwolfach.LongComponentTotalsAnyClass

@[expose] public section
/-! For an active ordinary hub, use all actual long components of its
factor to meet the same-sample reserved-interval demand. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_actual_interval_capacity
    {n K:ℕ} {U A B:Type} [Fintype U] [DecidableEq U] [Fintype A] [Fintype B]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (hn:0<n) (π:Equiv.Perm (Fin n)) (d m:ℕ) (hd:0<d) (θ:ℝ) (hθ:0<θ)
    (raw:RawIntervalFamilyOutcome (Fin n) U Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d raw false) t) (w:U)
    (index : A ⊕ B ≃ retainedAndRawIntervalIndex π d raw false true t J w)
    (hell:θ/100≤ordinaryAssignedFraction F hF K w none)
    (hcut:5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K+1)≤θ/2)
    (hlarge:4*((m:ℝ)+1)/(θ*(θ/100))<(n:ℝ)^((1:ℝ)/4))
    (hcounts:∀g,|rawIntervalHubStartCount π d g raw w-
      (n:ℝ)*ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w g/d|<(n:ℝ)^(3/4:ℝ)/d):
    let I:={C:(F w).ConnectedComponent // K<Fintype.card C}
    let components:I↪(F w).ConnectedComponent:=Function.Embedding.subtype _;
    Fintype.card (A⊕B)≤∑i:I,Fintype.card (components i)/((m+1)*d+5) :=by
  intro I components
  obtain ⟨hlong,htotal⟩:=long_component_totals_any_class hn F hF w
  apply ordinary_assigned_interval_capacity_from_start_counts F hF π d m (K+1) hd hn (by omega) θ hθ raw t J w index components hlong hell htotal
  · simpa only [Nat.cast_add,Nat.cast_one] using hcut
  · exact hlarge
  · exact hcounts
end Oberwolfach
