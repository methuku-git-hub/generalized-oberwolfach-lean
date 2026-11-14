module

public import Oberwolfach.InnerRequiredRawCount
public import Oberwolfach.LongAssignedUnassignedUpper

@[expose] public section
/-! Bound each inner required target set from the common sample's fixed-set
unassigned and retention tests, plus the unused-ordinary incidence bound. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_inner_required_targets_bound
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:0<n) (hK:0<K)
    (m d:ℕ) (hm:0<m) (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (θ:ℝ) (hθ:0≤θ) (hθ1:θ≤1) (π:Equiv.Perm (Fin n))
    (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (inner:Finset U) (vertices:Finset (Fin n)) (absorber occupied unused:U→Finset (Fin n))
    (happrox:∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inl true)→x∈occupied w)
    (hordinary:∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inr true)→x∈occupied w ∨ x∈unused w)
    (ζ:ℝ) (hrows:RetainedRestrictionGood π d σ false t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ J)
    (hfixed:∀w,|rawIntervalUnassignedHubCountOn π d σ w vertices-
      (vertices.card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(n:ℝ)^(3/4:ℝ)):
    ∀w,((innerRequiredTargets inner vertices (rawReservedSpokeList π d σ)
      (retainedFinalMarkedAt π d σ t J) absorber occupied w).card:ℝ)≤
      2*θ*vertices.card+(n:ℝ)^(3/4:ℝ)+ζ*n+((unused w∩vertices).card:ℝ):=by
  intro w
  have hc:=inner_required_targets_count_from_raw_cover π d σ t J inner vertices absorber occupied unused happrox hordinary ζ hrows w
  have hp:=long_assigned_unassigned_probability_at_most_two_theta hn hK m hm F hF θ hθ hθ1 w
  have hh:rawIntervalUnassignedHubCountOn π d σ w vertices<
      (vertices.card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))+(n:ℝ)^(3/4:ℝ):=by
    have hh:=(abs_lt.mp (hfixed w)).2
    linarith
  have hp':(vertices.card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
      (∑j,longAssignedSpokeProbability F hF K m θ w j))≤(vertices.card:ℝ)*(2*θ):=
    mul_le_mul_of_nonneg_left hp (by positivity)
  simp only [Fintype.card_fin] at hc
  nlinarith
end Oberwolfach
