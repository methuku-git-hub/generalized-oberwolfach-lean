module

public import Oberwolfach.OrdinaryActualIntervalCapacity
public import Oberwolfach.OrdinaryInactiveHubNoIntervals

@[expose] public section
/-! The same sampled interval family admits long-component block allocations at
both active and inactive ordinary hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_all_hub_interval_capacity
    {n K:ℕ} {U A B:Type} [Fintype U] [DecidableEq U] [Fintype A] [Fintype B]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (hn:0<n) (π:Equiv.Perm (Fin n)) (d m:ℕ) (hd:0<d) (θ:ℝ) (hθ:0<θ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t) (w:U)
    (index : A ⊕ B ≃ retainedAndRawIntervalIndex π d (fun e=>raw (Sum.inr e)) false true t J w)
    (hcut:5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K+1)≤θ/2)
    (hlarge:4*((m:ℝ)+1)/(θ*(θ/100))<(n:ℝ)^((1:ℝ)/4))
    (hcounts:∀g,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) w-
      (n:ℝ)*ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w g/d|<(n:ℝ)^(3/4:ℝ)/d)
    (hsupport:∀g v,rawMarkedPairSpokes π d raw g true true v w→
      ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w g≠0):
    let I:={C:(F w).ConnectedComponent // K<Fintype.card C}
    let components:I↪(F w).ConnectedComponent:=Function.Embedding.subtype _;
    Fintype.card (A⊕B)≤∑i:I,Fintype.card (components i)/((m+1)*d+5) :=by
  intro I components
  by_cases ha:θ/100≤ordinaryAssignedFraction F hF K w none
  · exact ordinary_actual_interval_capacity F hF hn π d m hd θ hθ (fun e=>raw (Sum.inr e)) t J w index ha hcut hlarge hcounts
  · have hz:=ordinary_inactive_hub_no_intervals F hF θ ((m:ℝ)+1) π d raw t J w (lt_of_not_ge ha) hsupport
    have hc:=Fintype.card_congr index
    rw [hz] at hc
    rw [hc]
    exact Nat.zero_le _
end Oberwolfach
