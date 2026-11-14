module

public import Oberwolfach.InnerRequiredRawOccurrence
public import Oberwolfach.LongAssignedUnassignedUpper

@[expose] public section
/-! The same fixed-inner column test controls occurrences of prescribed
inner labels, up to retained changes and unused ordinary labels. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_inner_required_occurrences_bound
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:0<n) (hK:0<K)
    (m d:ℕ) (hm:0<m) (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (θ:ℝ) (hθ:0≤θ) (hθ1:θ≤1) (π:Equiv.Perm (Fin n))
    (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (inner:Finset U) (vertices:Finset (Fin n)) (absorber occupied unused:U→Finset (Fin n))
    (happrox:∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inl true)→x∈occupied w)
    (hordinary:∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inr true)→x∈occupied w ∨ x∈unused w)
    (ζ:ℝ) (hrows:RetainedRestrictionGood π d σ false t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ J)
    (hcolumn:∀v,|rawIntervalUnassignedColumnCount π d σ v inner-
      ∑w∈inner,(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(n:ℝ)^(3/4:ℝ)):
    ∀v,(((Finset.univ:Finset U).filter (fun w=>v∈innerRequiredTargets inner vertices
      (rawReservedSpokeList π d σ) (retainedFinalMarkedAt π d σ t J) absorber occupied w)).card:ℝ)≤
      2*θ*inner.card+(n:ℝ)^(3/4:ℝ)+ζ*Fintype.card U+
      (((Finset.univ:Finset U).filter (fun w=>v∈unused w)).card:ℝ):=by
  intro v
  have hc:=inner_required_targets_occurrence_from_raw_cover π d σ t J inner vertices absorber occupied unused happrox hordinary ζ hrows v
  have hs:∑w∈inner,(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
      (∑j,longAssignedSpokeProbability F hF K m θ w j))≤∑_w∈inner,2*θ:=by
    apply Finset.sum_le_sum
    intro w hw
    exact long_assigned_unassigned_probability_at_most_two_theta hn hK m hm F hF θ hθ hθ1 w
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  have hcol:rawIntervalUnassignedColumnCount π d σ v inner<
      (∑w∈inner,(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j)))+(n:ℝ)^(3/4:ℝ):=by
    have hh:=(abs_lt.mp (hcolumn v)).2
    linarith
  nlinarith
end Oberwolfach
