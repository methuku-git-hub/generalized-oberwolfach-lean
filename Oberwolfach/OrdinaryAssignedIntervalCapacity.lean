module

public import Oberwolfach.OrdinaryReservedCapacityFromRpow
public import Oberwolfach.RetainedRawIntervalDemand
public import Oberwolfach.OrdinaryAssignedClassRecipe

@[expose] public section
/-! On an active ordinary-class hub, the original long-cycle fraction and
same-sample start counts supply enough disjoint buffered path blocks. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_interval_capacity_from_start_counts
    {n K:ℕ} {U I A B:Type} [Fintype U] [DecidableEq U] [Fintype I] [Fintype A] [Fintype B]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (π:Equiv.Perm (Fin n)) (d m cutoff:ℕ) (hd:0<d) (hn:0<n) (hcutoff:0<cutoff)
    (θ:ℝ) (hθ:0<θ)
    (raw:RawIntervalFamilyOutcome (Fin n) U Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d raw false) t) (w:U)
    (index : A ⊕ B ≃ retainedAndRawIntervalIndex π d raw false true t J w)
    (components:I↪(F w).ConnectedComponent)
    (hlong:∀i,cutoff≤Fintype.card (components i))
    (hell:θ/100≤ordinaryAssignedFraction F hF K w none)
    (htotal:((∑i,Fintype.card (components i):ℕ):ℝ)=ordinaryAssignedFraction F hF K w none*n)
    (hcut:5/(((m:ℝ)+1)*(d:ℝ)+5)+(((m:ℝ)+1)*(d:ℝ))/cutoff≤θ/2)
    (hlarge:4*((m:ℝ)+1)/(θ*(θ/100))<(n:ℝ)^((1:ℝ)/4))
    (hcounts:∀g,|rawIntervalHubStartCount π d g raw w-
      (n:ℝ)*ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w g/d|<(n:ℝ)^(3/4:ℝ)/d):
    Fintype.card (A⊕B)≤∑i,Fintype.card (components i)/((m+1)*d+5) :=by
  have hc:0<m+1:=by omega
  have hell0:0<θ/100:=by positivity
  have hclass:ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w false+
      ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w true≤
      (1-θ)*ordinaryAssignedFraction F hF K w none/(m+1):=by
    simp only [ordinaryAssignedMarkedProbability,ordinaryAssignedLongWeight,Bool.false_eq_true,ite_false,ite_true,
      if_neg (not_lt_of_ge hell),Nat.cast_add,Nat.cast_one,zero_add]
    exact le_rfl
  have hdem:=retained_raw_interval_demand_from_start_counts π d (m+1) hd hc
    raw false true t J w (ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1))
    θ (ordinaryAssignedFraction F hF K w none) (by simpa using hcounts) (by simpa only [Nat.cast_add,Nat.cast_one] using hclass)
  have hcard:=Fintype.card_congr index
  rw [←hcard] at hdem
  apply ordinary_reserved_capacity_from_rpow (fun i=>Fintype.card (components i)) (m+1) d cutoff
    (Fintype.card (A⊕B)) (n:ℝ) (ordinaryAssignedFraction F hF K w none) (θ/100) θ hc hd hcutoff
    (by exact_mod_cast hn) hθ hell0 hell hlong htotal
  · simpa using hcut
  · simpa using hlarge
  · simpa using hdem
end Oberwolfach
